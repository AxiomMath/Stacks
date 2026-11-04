module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Rational functions, generic local rings and the function field

Let `X` be a scheme with finitely many irreducible components. A rational function on `X` is
determined by its germs at the generic points of those components, and conversely any family of
such germs is realised by a rational function: the components can be separated by disjoint open
neighbourhoods (take the complement of the union of the other components), a germ is represented
by a section on a small open inside each, and the resulting sections glue over the — dense —
union. So `R(X) ≅ ∏_Z 𝒪_{X,η_Z}`, the product of the local rings at the generic points of the
irreducible components. This is Stacks 01RV.

Two specialisations follow. If `X` is reduced, each generic local ring is a field, namely the
residue field at the generic point, so `R(X) ≅ ∏_Z κ(η_Z)`. If `X` is integral there is only one
component, and `R(X)` is Mathlib's `AlgebraicGeometry.Scheme.functionField`, the stalk at the
generic point — in particular `R(X)` is a field.

Each identification is produced together with the formula for its action on a section over a
dense open (it sends `s ∈ Γ(X, U)` to the germs of `s`), which pins the isomorphism down rather
than merely asserting that one exists.

## Main definitions

* `Stacks.Chow.rationalFunctionsEquivStalks` — `R(X) ≅ ∏_Z 𝒪_{X,η_Z}`, with its action on
  sections (Stacks 01RV).
* `Stacks.Chow.rationalFunctionsEquivResidueFields` — the reduced case, `R(X) ≅ ∏_Z κ(η_Z)`.
* `Stacks.Chow.rationalFunctionsEquivFunctionField` — the integral case, `R(X) ≅ R(X)` in
  Mathlib's spelling `Scheme.functionField`.
* `Stacks.Chow.rationalFunctionsEquivResidueField` — the integral case against the residue
  field of the generic point.

## Main results

* `Stacks.Chow.isField_rationalFunctions` — the ring of rational functions of an integral
  scheme is a field, with the corresponding `Field` instance.

## Implementation notes

The product is indexed by Mathlib's `irreducibleComponents`, each factor taken at the canonical
generic point `Z.2.1.genericPoint` of the component. Surjectivity of the germ map is the gluing
argument above; the required disjointness is `componentNeighborhoods_disjoint`, and gluing uses
`AlgebraicGeometry.Scheme.Opens.iSupOpenCover` together with the observation that the overlaps
are empty, so the cocycle condition is vacuous. Injectivity is the local equality of two
representatives near each generic point, glued the same way.

`Stacks.Chow.rationalFunctionsEquivFunctionField` is the bridge to Mathlib's order of vanishing:
`AlgebraicGeometry.Scheme.ord` is defined on `Scheme.functionField`, so a principal divisor of a
rational function in the sense of Stacks 01RU is computed by transporting along this
equivalence.

## References

* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.AlgebraicGeometry.GenericPointDecomposition (affineLine coordinate lineHom)

/-! ### Separating the irreducible components -/

/-- The complement of the union of the irreducible components other than `Z`: an open set whose
closure is `Z` and which is disjoint from the corresponding set for any other component. -/
private def componentNeighborhood (X : Scheme.{u}) [Finite (irreducibleComponents X)]
    (Z : irreducibleComponents X) : X.Opens :=
  ⟨(⋃₀ (irreducibleComponents X \ {(Z : Set X)}))ᶜ, by
    rw [isOpen_compl_iff, Set.sUnion_eq_biUnion]
    exact (Set.toFinite (irreducibleComponents X)).sdiff.isClosed_biUnion fun W hW =>
      isClosed_of_mem_irreducibleComponents W hW.1⟩

/-- The canonical generic point of an irreducible component generates it. -/
private theorem isGenericPoint_component (X : Scheme.{u}) (Z : irreducibleComponents X) :
    IsGenericPoint Z.2.1.genericPoint (Z : Set X) :=
  Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)

private theorem componentNeighborhood_closure (X : Scheme.{u})
    [Finite (irreducibleComponents X)] (Z : irreducibleComponents X) :
    closure (componentNeighborhood X Z : Set X) = (Z : Set X) :=
  closure_sUnion_irreducibleComponents_sdiff_singleton
    (Set.toFinite (irreducibleComponents X)) (Z : Set X) Z.2

private theorem genericPoint_mem_componentNeighborhood (X : Scheme.{u})
    [Finite (irreducibleComponents X)] (Z : irreducibleComponents X) :
    Z.2.1.genericPoint ∈ componentNeighborhood X Z := by
  have hVne : (componentNeighborhood X Z : Set X).Nonempty := by
    rw [← closure_nonempty_iff, componentNeighborhood_closure]
    exact Z.2.1.nonempty
  obtain ⟨x, hx⟩ := hVne
  have hgen := isGenericPoint_component X Z
  apply hgen.mem_open_set_iff (componentNeighborhood X Z).2 |>.2
  refine ⟨x, ?_, hx⟩
  have hxcl : x ∈ closure (componentNeighborhood X Z : Set X) := subset_closure hx
  rw [componentNeighborhood_closure X Z] at hxcl
  exact hgen.def ▸ hxcl

private theorem componentNeighborhood_subset (X : Scheme.{u})
    [Finite (irreducibleComponents X)] (Z : irreducibleComponents X) :
    (componentNeighborhood X Z : Set X) ⊆ (Z : Set X) := fun _ hx =>
  (componentNeighborhood_closure X Z).le (subset_closure hx)

/-- A dense open set contains the generic point of every irreducible component. -/
private theorem genericPoint_mem_dense_open (X : Scheme.{u})
    [Finite (irreducibleComponents X)] (U : X.Opens) (hU : Dense (U : Set X))
    (Z : irreducibleComponents X) : Z.2.1.genericPoint ∈ U := by
  obtain ⟨x, hxV, hxU⟩ := hU.inter_open_nonempty _ (componentNeighborhood X Z).2
    ⟨_, genericPoint_mem_componentNeighborhood X Z⟩
  exact ((isGenericPoint_component X Z).mem_open_set_iff U.2).2
    ⟨x, componentNeighborhood_subset X Z hxV, hxU⟩

private theorem componentNeighborhoods_disjoint (X : Scheme.{u})
    [Finite (irreducibleComponents X)] (Z W : irreducibleComponents X) (hZW : Z ≠ W) :
    Disjoint (componentNeighborhood X Z : Set X) (componentNeighborhood X W : Set X) := by
  apply Set.disjoint_left.mpr
  intro x hxZ hxW
  have hWmem : (W : Set X) ∈ irreducibleComponents X \ {(Z : Set X)} :=
    ⟨W.2, fun he => hZW (Subtype.ext he.symm)⟩
  exact hxZ (Set.mem_sUnion.mpr ⟨(W : Set X), hWmem, componentNeighborhood_subset X W hxW⟩)

/-! ### Representing a family of germs by sections on disjoint opens -/

/-- A representative of a germ at the generic point of `Z` by a section on an open set inside
`componentNeighborhood X Z`. -/
private structure GenericLocalSection (X : Scheme.{u}) [Finite (irreducibleComponents X)]
    (Z : irreducibleComponents X) (a : X.presheaf.stalk Z.2.1.genericPoint) where
  /-- The open set on which the representing section lives. -/
  domain : X.Opens
  /-- It is contained in the chosen neighbourhood of the component. -/
  domain_le : domain ≤ componentNeighborhood X Z
  /-- It contains the generic point of the component. -/
  generic_mem : Z.2.1.genericPoint ∈ domain
  /-- The representing section. -/
  value : Γ(X, domain)
  /-- Its germ at the generic point is the prescribed one. -/
  germ_eq : X.presheaf.germ domain Z.2.1.genericPoint generic_mem value = a

private theorem exists_section_with_generic_germ (X : Scheme.{u})
    [Finite (irreducibleComponents X)] (Z : irreducibleComponents X)
    (a : X.presheaf.stalk Z.2.1.genericPoint) : Nonempty (GenericLocalSection X Z a) := by
  obtain ⟨W, hVW, hWη, s, hs⟩ :=
    X.presheaf.exists_le_germ_eq a (genericPoint_mem_componentNeighborhood X Z)
  exact ⟨⟨W, hVW, hWη, s, hs⟩⟩

private def localSectionOfGenericTuple (X : Scheme.{u}) [Finite (irreducibleComponents X)]
    (a : ∀ Z : irreducibleComponents X, X.presheaf.stalk Z.2.1.genericPoint) :
    ∀ Z : irreducibleComponents X, GenericLocalSection X Z (a Z) :=
  fun Z => Classical.choice (exists_section_with_generic_germ X Z (a Z))

private theorem topIso_restrict (X : Scheme.{u}) (U V : X.Opens) (h : V ≤ U)
    (t : Γ(U.toScheme, ⊤)) :
    X.presheaf.map (homOfLE h).op (U.topIso.hom t) =
      V.topIso.hom ((X.homOfLE h).appTop t) := by
  have hn := (Scheme.restrictFunctorΓ (X := X)).hom.naturality (homOfLE h).op
  change (X.homOfLE h).appTop ≫ V.topIso.hom =
    U.topIso.hom ≫ X.presheaf.map (homOfLE h).op at hn
  exact (congrArg (fun f => f t) hn).symm

/-- The union of a family of opens containing the generic point of every irreducible component
is dense. -/
private theorem dense_iSup_of_generic_mem (X : Scheme.{u})
    [Finite (irreducibleComponents X)] (U : irreducibleComponents X → X.Opens)
    (hU : ∀ Z, Z.2.1.genericPoint ∈ U Z) : Dense (⨆ Z, (U Z : Set X)) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro x
  have hxall : x ∈ ⋃₀ irreducibleComponents X := by
    rw [sUnion_irreducibleComponents]
    simp
  obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.mp hxall
  let i : irreducibleComponents X := ⟨Z, hZ⟩
  have hgen : closure ({i.2.1.genericPoint} : Set X) = (i : Set X) :=
    (isGenericPoint_component X i).def
  have hxclosure : x ∈ closure ({i.2.1.genericPoint} : Set X) := hgen.symm ▸ hxZ
  exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_iUnion.mpr ⟨i, hU i⟩)) hxclosure

/-! ### The coordinate section of a partial map -/

/-- The section of the structure sheaf corresponding to a partial map to the affine line: the
pullback of the coordinate. -/
private def coordinateSection (X : Scheme.{u}) (p : X.PartialMap affineLine) :
    Γ(X, p.domain) :=
  p.domain.topIso.hom (p.hom.appTop coordinate)

private theorem coordinateSection_map_restrict (X : Scheme.{u})
    (p : X.PartialMap affineLine) (V : X.Opens) (h : V ≤ p.domain) :
    V.topIso.hom ((X.homOfLE h).appTop (p.hom.appTop coordinate)) =
      X.presheaf.map (homOfLE h).op (coordinateSection X p) := by
  rw [← topIso_restrict X p.domain V h (p.hom.appTop coordinate)]
  rfl

private theorem coordinateSection_restrict (X : Scheme.{u}) (p : X.PartialMap affineLine)
    (V : X.Opens) (hV : Dense (V : Set X)) (h : V ≤ p.domain) :
    coordinateSection X (p.restrict V hV h) =
      V.topIso.hom ((X.homOfLE h).appTop (p.hom.appTop coordinate)) := by
  show V.topIso.hom ((X.homOfLE h ≫ p.hom).appTop coordinate) = _
  rw [Scheme.Hom.comp_appTop]
  rfl

private theorem coordinateSection_restrict_eq (X : Scheme.{u}) (p : X.PartialMap affineLine)
    (V : X.Opens) (hV : Dense (V : Set X)) (h : V ≤ p.domain) :
    coordinateSection X (p.restrict V hV h) =
      X.presheaf.map (homOfLE h).op (coordinateSection X p) := by
  rw [coordinateSection_restrict, coordinateSection_map_restrict]

private theorem partialMap_eq_of_coordinateSection (X : Scheme.{u})
    (p : X.PartialMap affineLine) :
    p.hom = AffineSpace.homOfVector (specULiftZIsTerminal.from p.domain.toScheme)
      (fun _ : ULift.{u} (Fin 1) => p.domain.topIso.inv (coordinateSection X p)) := by
  apply AffineSpace.hom_ext
  · exact specULiftZIsTerminal.hom_ext _ _
  · intro i
    obtain rfl : i = ⟨0⟩ := Subsingleton.elim _ _
    rw [AffineSpace.homOfVector_appTop_coord]
    exact (Iso.hom_inv_id_apply p.domain.topIso (p.hom.appTop coordinate)).symm

private theorem partialMap_toRationalMap_eq_ofSection (X : Scheme.{u})
    (p : X.PartialMap affineLine) :
    p.toRationalMap =
      ofSection X ⟨p.domain, p.dense_domain⟩ (coordinateSection X p) := by
  rw [ofSection]
  let q : X.PartialMap affineLine :=
    ⟨p.domain, p.dense_domain, AffineSpace.homOfVector
      (specULiftZIsTerminal.from p.domain.toScheme)
      (fun _ : ULift.{u} (Fin 1) => p.domain.topIso.inv (coordinateSection X p))⟩
  have hdom : p.domain = q.domain := rfl
  have hhom : p.hom = (X.isoOfEq hdom).hom ≫ q.hom := by
    simpa [q, hdom] using partialMap_eq_of_coordinateSection X p
  exact congrArg Scheme.PartialMap.toRationalMap (Scheme.PartialMap.ext p q hdom hhom)

private theorem coordinateSection_ofSection (X : Scheme.{u}) (U : DenseOpen X)
    (s : Γ(X, U.1)) :
    coordinateSection X
      (⟨U.1, U.2, AffineSpace.homOfVector (specULiftZIsTerminal.from U.1.toScheme)
        (fun _ : ULift.{u} (Fin 1) => U.1.topIso.inv s)⟩ : X.PartialMap affineLine) = s := by
  show U.1.topIso.hom
    ((AffineSpace.homOfVector (specULiftZIsTerminal.from U.1.toScheme)
      (fun _ : ULift.{u} (Fin 1) => U.1.topIso.inv s)).appTop coordinate) = s
  rw [AffineSpace.homOfVector_appTop_coord]
  exact Iso.inv_hom_id_apply U.1.topIso s

private theorem ofSection_eq_partialMap (X : Scheme.{u}) (U : DenseOpen X) (s : Γ(X, U.1)) :
    ofSection X U s =
      ((⟨U.1, U.2, AffineSpace.homOfVector (specULiftZIsTerminal.from U.1.toScheme)
        (fun _ : ULift.{u} (Fin 1) => U.1.topIso.inv s)⟩ :
          X.PartialMap affineLine).toRationalMap) := rfl

/-! ### Gluing sections on a disjoint family of opens -/

/-- The morphism to the affine line glued from sections on a pairwise disjoint family of opens,
together with its restrictions. -/
private structure DisjointSectionsAssembly (X : Scheme.{u}) {ι : Type*} (V : ι → X.Opens)
    (s : ∀ i, Γ(X, V i)) where
  /-- The glued morphism on the union. -/
  hom : (⨆ i, V i : X.Opens).toScheme ⟶ affineLine
  /-- Its restriction to each member of the family. -/
  localMap : ∀ i, (V i).toScheme ⟶ affineLine
  /-- The restriction is really the restriction. -/
  hom_restrict : ∀ i, (Scheme.Opens.iSupOpenCover V).f i ≫ hom = localMap i
  /-- Each local morphism has the prescribed section as its coordinate. -/
  localMap_section : ∀ i,
    AffineSpace.homOfVector (specULiftZIsTerminal.from (V i).toScheme)
      (fun _ : ULift.{u} (Fin 1) => (V i).topIso.inv (s i)) = localMap i

private def glueDisjointSections (X : Scheme.{u}) {ι : Type*} (V : ι → X.Opens)
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i : Set X) (V j : Set X)) (s : ∀ i, Γ(X, V i)) :
    DisjointSectionsAssembly X V s := by
  let U : X.Opens := ⨆ i, V i
  let 𝒰 : U.toScheme.OpenCover := Scheme.Opens.iSupOpenCover V
  let f : ∀ i, 𝒰.X i ⟶ affineLine := fun i =>
    AffineSpace.homOfVector (specULiftZIsTerminal.from (V i).toScheme)
      (fun _ : ULift.{u} (Fin 1) => (V i).topIso.inv (s i))
  have hf : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd _ _ ≫ f j := by
    intro i j
    by_cases hij : i = j
    · subst j
      have hfst : pullback.fst (𝒰.f i) (𝒰.f i) = pullback.snd (𝒰.f i) (𝒰.f i) :=
        (cancel_mono (𝒰.f i)).mp pullback.condition
      rw [hfst]
    · have hempty : IsEmpty ↑(pullback (𝒰.f i) (𝒰.f j)) :=
        Scheme.isEmpty_pullback _ _ (by
          rw [Set.disjoint_iff_forall_ne]
          intro x hx y hy hxy
          obtain ⟨a, rfl⟩ := hx
          obtain ⟨b, hb⟩ := hy
          have hab : a.1 = b.1 := by
            have hxy'' : (X.homOfLE (le_iSup V i) a).1 =
                (X.homOfLE (le_iSup V j) b).1 := by
              convert congrArg Subtype.val (hxy.trans hb.symm) using 1 <;> rfl
            calc
              a.1 = (X.homOfLE (le_iSup V i) a).1 := (Scheme.homOfLE_apply _ _).symm
              _ = (X.homOfLE (le_iSup V j) b).1 := hxy''
              _ = b.1 := Scheme.homOfLE_apply _ _
          have haV : a.1 ∈ V i := by simpa [𝒰] using a.2
          have hbV : b.1 ∈ V j := by simpa [𝒰] using b.2
          have hij' : (i : ι) ≠ (j : ι) := by simpa [𝒰] using hij
          exact (Set.disjoint_left.mp (hdisj i j hij')) haV (hab ▸ hbV))
      exact IsInitial.hom_ext (isInitialOfIsEmpty (X := pullback (𝒰.f i) (𝒰.f j))) _ _
  exact ⟨𝒰.glueMorphisms f hf, f, fun i => 𝒰.ι_glueMorphisms f hf i, fun _ => rfl⟩

private def genericTupleAssembly (X : Scheme.{u}) [Finite (irreducibleComponents X)]
    (a : ∀ Z : irreducibleComponents X, X.presheaf.stalk Z.2.1.genericPoint) :
    DisjointSectionsAssembly X (fun Z => (localSectionOfGenericTuple X a Z).domain)
      (fun Z => (localSectionOfGenericTuple X a Z).value) := by
  let q := localSectionOfGenericTuple X a
  let U : irreducibleComponents X → X.Opens := fun Z => (q Z).domain
  have hdisj : ∀ Z W, Z ≠ W → Disjoint (U Z : Set X) (U W : Set X) := fun Z W hZW =>
    (componentNeighborhoods_disjoint X Z W hZW).mono ((q Z).domain_le) ((q W).domain_le)
  exact glueDisjointSections X U hdisj (fun Z => (q Z).value)

/-- The partial map to the affine line realising a prescribed family of germs. -/
private def genericTuplePartialMap (X : Scheme.{u}) [Finite (irreducibleComponents X)]
    (a : ∀ Z : irreducibleComponents X, X.presheaf.stalk Z.2.1.genericPoint) :
    X.PartialMap affineLine := by
  let q := localSectionOfGenericTuple X a
  let U : irreducibleComponents X → X.Opens := fun Z => (q Z).domain
  refine ⟨⨆ Z, U Z, ?_, (genericTupleAssembly X a).hom⟩
  simpa [Opens.coe_iSup] using dense_iSup_of_generic_mem X U fun Z => (q Z).generic_mem

/-! ### The germ map on rational functions -/

/-- The germ at the generic point of a component of the coordinate section of a partial map. -/
private def partialGenericValue (X : Scheme.{u}) [Finite (irreducibleComponents X)]
    (p : X.PartialMap affineLine) (Z : irreducibleComponents X) :
    X.presheaf.stalk Z.2.1.genericPoint :=
  X.presheaf.germ p.domain Z.2.1.genericPoint
    (genericPoint_mem_dense_open X p.domain p.dense_domain Z) (coordinateSection X p)

private theorem partialGenericValue_genericTuplePartialMap (X : Scheme.{u})
    [Finite (irreducibleComponents X)]
    (a : ∀ Z : irreducibleComponents X, X.presheaf.stalk Z.2.1.genericPoint)
    (Z : irreducibleComponents X) :
    partialGenericValue X (genericTuplePartialMap X a) Z = a Z := by
  let q := localSectionOfGenericTuple X a
  let U : irreducibleComponents X → X.Opens := fun W => (q W).domain
  let A := genericTupleAssembly X a
  have hdom : U Z ≤ (genericTuplePartialMap X a).domain := le_iSup U Z
  have hglue : X.homOfLE hdom ≫ (genericTuplePartialMap X a).hom = A.localMap Z := by
    rw [Subsingleton.elim hdom (le_iSup U Z)]
    show (Scheme.Opens.iSupOpenCover U).f Z ≫ A.hom = A.localMap Z
    exact A.hom_restrict Z
  have happ : (X.homOfLE hdom).appTop
      ((genericTuplePartialMap X a).hom.appTop coordinate) =
        (A.localMap Z).appTop coordinate := by
    have hh := congrArg (fun k => k.appTop coordinate) hglue
    rwa [Scheme.Hom.comp_appTop] at hh
  rw [partialGenericValue, ← X.presheaf.germ_res_apply (homOfLE hdom)
    Z.2.1.genericPoint (q Z).generic_mem, ← coordinateSection_map_restrict, happ]
  show X.presheaf.germ (U Z) Z.2.1.genericPoint (q Z).generic_mem
    ((U Z).topIso.hom ((A.localMap Z).appTop coordinate)) = a Z
  rw [← A.localMap_section Z, AffineSpace.homOfVector_appTop_coord]
  show X.presheaf.germ (U Z) Z.2.1.genericPoint (q Z).generic_mem
    ((U Z).topIso.hom ((U Z).topIso.inv (q Z).value)) = a Z
  rw [Iso.inv_hom_id_apply]
  simpa [U, q] using (q Z).germ_eq

private theorem partialGenericValue_eq_of_equiv (X : Scheme.{u})
    [Finite (irreducibleComponents X)] (p q : X.PartialMap affineLine) (hpq : p.equiv q)
    (Z : irreducibleComponents X) :
    partialGenericValue X p Z = partialGenericValue X q Z := by
  obtain ⟨W, hW, hWp, hWq, heq⟩ := hpq
  let η := Z.2.1.genericPoint
  have hη : η ∈ W := genericPoint_mem_dense_open X W hW Z
  have hcoord : coordinateSection X (p.restrict W hW hWp) =
      coordinateSection X (q.restrict W hW hWq) :=
    congrArg (fun m : W.toScheme ⟶ affineLine =>
      W.topIso.hom (m.appTop coordinate)) heq
  calc
    partialGenericValue X p Z =
        X.presheaf.germ W η hη
          (X.presheaf.map (homOfLE hWp).op (coordinateSection X p)) :=
      (X.presheaf.germ_res_apply (homOfLE hWp) η hη (coordinateSection X p)).symm
    _ = X.presheaf.germ W η hη (coordinateSection X (p.restrict W hW hWp)) := by
      rw [coordinateSection_restrict_eq]
    _ = X.presheaf.germ W η hη (coordinateSection X (q.restrict W hW hWq)) := by rw [hcoord]
    _ = X.presheaf.germ W η hη
        (X.presheaf.map (homOfLE hWq).op (coordinateSection X q)) := by
      rw [coordinateSection_restrict_eq]
    _ = partialGenericValue X q Z :=
      X.presheaf.germ_res_apply (homOfLE hWq) η hη (coordinateSection X q)

/-- The family of germs of a rational function at the generic points of the irreducible
components. -/
private def genericStalkValues (X : Scheme.{u}) [Finite (irreducibleComponents X)] :
    rationalFunctions X →
      (∀ Z : irreducibleComponents X, X.presheaf.stalk Z.2.1.genericPoint) :=
  Quotient.lift (fun p Z => partialGenericValue X p Z)
    (fun _ _ hpq => funext fun Z => partialGenericValue_eq_of_equiv X _ _ hpq Z)

/-- An open neighbourhood of the generic point of `Z` on which two partial maps agree. -/
private structure LocalEqualityNeighborhood (X : Scheme.{u}) (p q : X.PartialMap affineLine)
    (Z : irreducibleComponents X) where
  /-- The neighbourhood. -/
  domain : X.Opens
  /-- It contains the generic point of the component. -/
  generic_mem : Z.2.1.genericPoint ∈ domain
  /-- It lies in the domain of the first map. -/
  domain_le_p : domain ≤ p.domain
  /-- It lies in the domain of the second map. -/
  domain_le_q : domain ≤ q.domain
  /-- The two maps agree there. -/
  hom_eq : X.homOfLE domain_le_p ≫ p.hom = X.homOfLE domain_le_q ≫ q.hom

private theorem exists_localEqualityNeighborhood (X : Scheme.{u})
    [Finite (irreducibleComponents X)] (p q : X.PartialMap affineLine)
    (h : ∀ Z, partialGenericValue X p Z = partialGenericValue X q Z)
    (Z : irreducibleComponents X) : Nonempty (LocalEqualityNeighborhood X p q Z) := by
  have hp : Z.2.1.genericPoint ∈ p.domain :=
    genericPoint_mem_dense_open X p.domain p.dense_domain Z
  have hq : Z.2.1.genericPoint ∈ q.domain :=
    genericPoint_mem_dense_open X q.domain q.dense_domain Z
  obtain ⟨W, hWη, iP, iQ, hsections⟩ := X.presheaf.germ_eq
    Z.2.1.genericPoint hp hq (coordinateSection X p) (coordinateSection X q) (h Z)
  let hWp : W ≤ p.domain := iP.le
  let hWq : W ≤ q.domain := iQ.le
  have hiP : iP = homOfLE hWp := Subsingleton.elim _ _
  have hiQ : iQ = homOfLE hWq := Subsingleton.elim _ _
  rw [hiP, hiQ] at hsections
  have hcoord : (X.homOfLE hWp).appTop (p.hom.appTop coordinate) =
      (X.homOfLE hWq).appTop (q.hom.appTop coordinate) := by
    have htop : (Scheme.Opens.topIso (X := X) W).hom
          ((X.homOfLE hWp).appTop (p.hom.appTop coordinate)) =
        (Scheme.Opens.topIso (X := X) W).hom
          ((X.homOfLE hWq).appTop (q.hom.appTop coordinate)) := by
      simpa only [coordinateSection_map_restrict] using hsections
    simpa only [Iso.hom_inv_id_apply] using congrArg (Scheme.Opens.topIso (X := X) W).inv htop
  have hhom : X.homOfLE hWp ≫ p.hom = X.homOfLE hWq ≫ q.hom := by
    apply AffineSpace.hom_ext
    · exact specULiftZIsTerminal.hom_ext _ _
    · intro i
      obtain rfl : i = ⟨0⟩ := Subsingleton.elim _ _
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
      exact hcoord
  exact ⟨⟨W, hWη, hWp, hWq, hhom⟩⟩

private def localEqualityNeighborhoods (X : Scheme.{u}) [Finite (irreducibleComponents X)]
    (p q : X.PartialMap affineLine)
    (h : ∀ Z, partialGenericValue X p Z = partialGenericValue X q Z) :
    ∀ Z : irreducibleComponents X, LocalEqualityNeighborhood X p q Z :=
  fun Z => Classical.choice (exists_localEqualityNeighborhood X p q h Z)

private theorem rationalMap_eq_of_partialGenericValue_eq (X : Scheme.{u})
    [Finite (irreducibleComponents X)] (p q : X.PartialMap affineLine)
    (h : ∀ Z, partialGenericValue X p Z = partialGenericValue X q Z) :
    p.toRationalMap = q.toRationalMap := by
  let N := localEqualityNeighborhoods X p q h
  let V : irreducibleComponents X → X.Opens := fun Z => (N Z).domain
  have hV : Dense ((⨆ Z, V Z : X.Opens) : Set X) := by
    simpa [Opens.coe_iSup] using dense_iSup_of_generic_mem X V fun Z => (N Z).generic_mem
  have hVp : (⨆ Z, V Z : X.Opens) ≤ p.domain := iSup_le fun Z => (N Z).domain_le_p
  have hVq : (⨆ Z, V Z : X.Opens) ≤ q.domain := iSup_le fun Z => (N Z).domain_le_q
  have hhom : (p.restrict (⨆ Z, V Z) hV hVp).hom = (q.restrict (⨆ Z, V Z) hV hVq).hom := by
    apply (Scheme.Opens.iSupOpenCover V).hom_ext
    intro Z
    simpa [Scheme.Opens.iSupOpenCover, Scheme.PartialMap.restrict] using (N Z).hom_eq
  exact Scheme.PartialMap.toRationalMap_eq_iff.mpr ⟨⨆ Z, V Z, hV, hVp, hVq, hhom⟩

private theorem genericStalkValues_toRationalMap (X : Scheme.{u})
    [Finite (irreducibleComponents X)] (p : X.PartialMap affineLine) :
    genericStalkValues X p.toRationalMap = fun Z => partialGenericValue X p Z := rfl

private theorem genericStalkValues_bijective (X : Scheme.{u})
    [Finite (irreducibleComponents X)] : Function.Bijective (genericStalkValues X) := by
  refine ⟨fun f g hfg => ?_, fun a => ⟨(genericTuplePartialMap X a).toRationalMap,
    funext (partialGenericValue_genericTuplePartialMap X a)⟩⟩
  obtain ⟨p, rfl⟩ := Scheme.PartialMap.toRationalMap_surjective f
  obtain ⟨q, rfl⟩ := Scheme.PartialMap.toRationalMap_surjective g
  exact rationalMap_eq_of_partialGenericValue_eq X p q (congrFun hfg)

private theorem partialMap_eq_ofSection_on_smaller_dense_open (X : Scheme.{u})
    (p : X.PartialMap affineLine) (V : X.Opens) (hV : Dense (V : Set X)) (h : V ≤ p.domain) :
    p.toRationalMap =
      ofSection X ⟨V, hV⟩ (X.presheaf.map (homOfLE h).op (coordinateSection X p)) := by
  calc
    p.toRationalMap = (p.restrict V hV h).toRationalMap :=
      (p.restrict_toRationalMap V hV h).symm
    _ = ofSection X ⟨V, hV⟩ (coordinateSection X (p.restrict V hV h)) :=
      partialMap_toRationalMap_eq_ofSection X (p.restrict V hV h)
    _ = ofSection X ⟨V, hV⟩ (X.presheaf.map (homOfLE h).op (coordinateSection X p)) := by
      rw [coordinateSection_restrict_eq]

private theorem genericStalkValues_ofSection (X : Scheme.{u})
    [Finite (irreducibleComponents X)] (U : DenseOpen X) (s : Γ(X, U.1)) :
    genericStalkValues X (ofSection X U s) = fun Z =>
      X.presheaf.germ U.1 Z.2.1.genericPoint
        (genericPoint_mem_dense_open X U.1 U.2 Z) s := by
  funext Z
  rw [ofSection_eq_partialMap, genericStalkValues_toRationalMap]
  simp [partialGenericValue, coordinateSection_ofSection]

/-- Any two rational functions are given by sections over a common dense open. -/
private theorem exists_common_dense_open_sections (X : Scheme.{u})
    (f g : rationalFunctions X) :
    ∃ (U : DenseOpen X) (s t : Γ(X, U.1)), f = ofSection X U s ∧ g = ofSection X U t := by
  obtain ⟨p, rfl⟩ := Scheme.PartialMap.toRationalMap_surjective f
  obtain ⟨q, rfl⟩ := Scheme.PartialMap.toRationalMap_surjective g
  exact ⟨⟨p.domain ⊓ q.domain, p.dense_domain.inter_of_isOpen_left q.dense_domain p.domain.2⟩,
    _, _, partialMap_eq_ofSection_on_smaller_dense_open X p (p.domain ⊓ q.domain) _ inf_le_left,
    partialMap_eq_ofSection_on_smaller_dense_open X q (p.domain ⊓ q.domain) _ inf_le_right⟩

private theorem genericStalkValues_add (X : Scheme.{u}) [Finite (irreducibleComponents X)]
    (f g : rationalFunctions X) :
    genericStalkValues X (f + g) = genericStalkValues X f + genericStalkValues X g := by
  obtain ⟨U, s, t, rfl, rfl⟩ := exists_common_dense_open_sections X f g
  have hsum : ofSection X U s + ofSection X U t = ofSection X U (s + t) := by
    simpa only [ofSectionRingHom_apply] using ((ofSectionRingHom X U).map_add s t).symm
  rw [hsum, genericStalkValues_ofSection, genericStalkValues_ofSection,
    genericStalkValues_ofSection]
  funext Z
  exact (X.presheaf.germ U.1 Z.2.1.genericPoint
    (genericPoint_mem_dense_open X U.1 U.2 Z)).hom.map_add s t

private theorem genericStalkValues_mul (X : Scheme.{u}) [Finite (irreducibleComponents X)]
    (f g : rationalFunctions X) :
    genericStalkValues X (f * g) = genericStalkValues X f * genericStalkValues X g := by
  obtain ⟨U, s, t, rfl, rfl⟩ := exists_common_dense_open_sections X f g
  have hmul : ofSection X U s * ofSection X U t = ofSection X U (s * t) := by
    simpa only [ofSectionRingHom_apply] using ((ofSectionRingHom X U).map_mul s t).symm
  rw [hmul, genericStalkValues_ofSection, genericStalkValues_ofSection,
    genericStalkValues_ofSection]
  funext Z
  exact (X.presheaf.germ U.1 Z.2.1.genericPoint
    (genericPoint_mem_dense_open X U.1 U.2 Z)).hom.map_mul s t

/-- The germ map, as a ring homomorphism. -/
private def genericStalkValuesRingHom (X : Scheme.{u}) [Finite (irreducibleComponents X)] :
    rationalFunctions X →+*
      (∀ Z : irreducibleComponents X, X.presheaf.stalk Z.2.1.genericPoint) where
  toFun := genericStalkValues X
  map_zero' := by
    let U : DenseOpen X := ⟨⊤, dense_univ⟩
    have hz : ofSection X U 0 = 0 := by
      simpa only [ofSectionRingHom_apply] using (ofSectionRingHom X U).map_zero
    rw [← hz, genericStalkValues_ofSection]
    funext Z
    exact (X.presheaf.germ U.1 Z.2.1.genericPoint
      (genericPoint_mem_dense_open X U.1 U.2 Z)).hom.map_zero
  map_one' := by
    let U : DenseOpen X := ⟨⊤, dense_univ⟩
    have h1 : ofSection X U 1 = 1 := by
      simpa only [ofSectionRingHom_apply] using (ofSectionRingHom X U).map_one
    rw [← h1, genericStalkValues_ofSection]
    funext Z
    exact (X.presheaf.germ U.1 Z.2.1.genericPoint
      (genericPoint_mem_dense_open X U.1 U.2 Z)).hom.map_one
  map_add' := genericStalkValues_add X
  map_mul' := genericStalkValues_mul X

private theorem isField_genericComponentStalk (X : Scheme.{u})
    [Finite (irreducibleComponents X)] [IsReduced X] (Z : irreducibleComponents X) :
    IsField (X.presheaf.stalk Z.2.1.genericPoint) := by
  apply isField_stalk_of_closure_mem_irreducibleComponents X Z.2.1.genericPoint
  rw [(isGenericPoint_component X Z).def]
  exact Z.2

private def genericStalkResidueEquiv (X : Scheme.{u}) [Finite (irreducibleComponents X)]
    [IsReduced X] (Z : irreducibleComponents X) :
    X.presheaf.stalk Z.2.1.genericPoint ≃+* X.residueField Z.2.1.genericPoint := by
  let R := X.presheaf.stalk Z.2.1.genericPoint
  let _ : Field R := (isField_genericComponentStalk X Z).toField
  have hker : RingHom.ker (X.residue Z.2.1.genericPoint).hom = ⊥ := by
    change RingHom.ker (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) = ⊥
    rw [Ideal.mk_ker, IsLocalRing.maximalIdeal_eq_bot]
  exact RingEquiv.ofBijective (X.residue Z.2.1.genericPoint).hom
    ⟨(RingHom.injective_iff_ker_eq_bot _).mpr hker, X.residue_surjective Z.2.1.genericPoint⟩

private theorem genericStalkResidueEquiv_apply (X : Scheme.{u})
    [Finite (irreducibleComponents X)] [IsReduced X] (Z : irreducibleComponents X)
    (a : X.presheaf.stalk Z.2.1.genericPoint) :
    genericStalkResidueEquiv X Z a = X.residue Z.2.1.genericPoint a := rfl

/-! ### The identifications -/

/-- **Stacks 01RV.** The rational functions of a scheme with finitely many irreducible
components are the product of the local rings at the generic points of those components; the
identification sends a section on a dense open to its family of germs. -/
@[stacks 01RV "product of generic local rings",
  no_expose,
  ega "I 7.1.13" "more general",
  ega "I 7.1.5" "more general",
  ega "I 7.1.8" "partial",
  ega "I 7.3.3" "partial", sga "1 I 10.3" "more general", sga "4 IX 4.0" "partial"]
def rationalFunctionsEquivStalks (X : Scheme.{u}) [Finite (irreducibleComponents X)] :
    { e : rationalFunctions X ≃+*
        (∀ Z : irreducibleComponents X, X.presheaf.stalk Z.2.1.genericPoint) //
      ∀ (U : DenseOpen X) (s : Γ(X, U.1)) (Z : irreducibleComponents X)
        (h : Z.2.1.genericPoint ∈ U.1),
        e (ofSection X U s) Z = X.presheaf.germ U.1 Z.2.1.genericPoint h s } :=
  ⟨RingEquiv.ofBijective (genericStalkValuesRingHom X) (genericStalkValues_bijective X),
    fun U s Z _ => congrFun (genericStalkValues_ofSection X U s) Z⟩

/-- **Stacks 01RV.** On a reduced scheme the generic local rings are the residue fields at the
generic points, so the rational functions are their product. -/
@[stacks 01RV "product of generic residue fields",
  no_expose,
  ega "I 7.3.3" "special case",
  sga "1 I 10.3" "special case",
  sga "4 IX 4.0" "special case"]
def rationalFunctionsEquivResidueFields (X : Scheme.{u}) [Finite (irreducibleComponents X)]
    [IsReduced X] :
    { e : rationalFunctions X ≃+*
        (∀ Z : irreducibleComponents X, X.residueField Z.2.1.genericPoint) //
      ∀ (U : DenseOpen X) (s : Γ(X, U.1)) (Z : irreducibleComponents X)
        (h : Z.2.1.genericPoint ∈ U.1),
        e (ofSection X U s) Z = X.evaluation U.1 Z.2.1.genericPoint h s } := by
  let e0 := (rationalFunctionsEquivStalks X).1
  let e1 := RingEquiv.piCongrRight (fun Z => genericStalkResidueEquiv X Z)
  refine ⟨e0.trans e1, fun U s Z h => ?_⟩
  change genericStalkResidueEquiv X Z (e0 (ofSection X U s) Z) = _
  rw [(rationalFunctionsEquivStalks X).2 U s Z h, genericStalkResidueEquiv_apply]
  rfl

/-- **Stacks 01RV.** On an integral scheme the rational functions are the function field, that
is, the stalk at the generic point. -/
@[stacks 01RV "integral function field", ega "I 7.1.5" "integral case"]
def rationalFunctionsEquivFunctionField (X : Scheme.{u}) [IsIntegral X] :
    { e : rationalFunctions X ≃+* X.functionField //
      ∀ (U : DenseOpen X) (s : Γ(X, U.1)) (h : genericPoint X ∈ U.1),
        e (ofSection X U s) = X.presheaf.germ U.1 (genericPoint X) h s } := by
  letI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  letI : Unique (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  let Z : irreducibleComponents X := default
  have hcomp : (Z : Set X) = Set.univ :=
    congrArg Subtype.val (Subsingleton.elim Z ⟨Set.univ, by
      rw [irreducibleComponents_eq_singleton]
      simp⟩)
  have hgenericZ : IsGenericPoint Z.2.1.genericPoint (Set.univ : Set X) := by
    rw [← hcomp]
    exact Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)
  have hη : Z.2.1.genericPoint = genericPoint X := hgenericZ.eq (genericPoint_spec X)
  let eCast : X.presheaf.stalk Z.2.1.genericPoint ≃+* X.functionField :=
    (X.presheaf.stalkCongr (Inseparable.of_eq hη)).commRingCatIsoToRingEquiv
  let e1 : (∀ Z : irreducibleComponents X,
      X.presheaf.stalk Z.2.1.genericPoint) ≃+* X.functionField :=
    (RingEquiv.piUnique (fun (Z : irreducibleComponents X) =>
      X.presheaf.stalk Z.2.1.genericPoint)).trans eCast
  refine ⟨(rationalFunctionsEquivStalks X).1.trans e1, ?_⟩
  intro U s h
  have hZ : Z.2.1.genericPoint ∈ U.1 := hη ▸ h
  change eCast ((rationalFunctionsEquivStalks X).1 (ofSection X U s) Z) = _
  rw [(rationalFunctionsEquivStalks X).2 U s Z hZ]
  change ((X.presheaf.stalkCongr (Inseparable.of_eq hη)).hom
      (X.presheaf.germ U.1 Z.2.1.genericPoint hZ s)) = _
  have hspec : genericPoint X ⤳ Z.2.1.genericPoint := by rw [← hη]
  rw [TopCat.Presheaf.stalkCongr_hom]
  change (X.presheaf.germ U.1 Z.2.1.genericPoint hZ ≫
    X.presheaf.stalkSpecializes hspec) s = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]

/-- **Stacks 01RV.** On an integral scheme the rational functions are the residue field of the
generic point. -/
@[stacks 01RV "integral residue field", ega "I 7.1.5" "κ(η) when integral"]
def rationalFunctionsEquivResidueField (X : Scheme.{u}) [IsIntegral X] :
    { e : rationalFunctions X ≃+* X.residueField (genericPoint X) //
      ∀ (U : DenseOpen X) (s : Γ(X, U.1)) (h : genericPoint X ∈ U.1),
        e (ofSection X U s) = X.evaluation U.1 (genericPoint X) h s } := by
  let e0 := (rationalFunctionsEquivFunctionField X).1
  let e1 : X.functionField ≃+* X.residueField (genericPoint X) :=
    RingEquiv.ofBijective (X.residue (genericPoint X)).hom
      ⟨(X.residue (genericPoint X)).hom.injective, X.residue_surjective (genericPoint X)⟩
  refine ⟨e0.trans e1, fun U s h => ?_⟩
  change e1 (e0 (ofSection X U s)) = _
  rw [(rationalFunctionsEquivFunctionField X).2 U s h]
  change X.residue (genericPoint X) (X.presheaf.germ U.1 (genericPoint X) h s) = _
  rfl

/-- **Stacks 01RV.** The ring of rational functions of an integral scheme is a field. -/
@[stacks 01RV "field property", ega "I 7.1.5" "field when integral", ega "I 7.1.8" "special case"]
theorem isField_rationalFunctions (X : Scheme.{u}) [IsIntegral X] :
    IsField (rationalFunctions X) :=
  ((rationalFunctionsEquivFunctionField X).1.toMulEquiv).isField
    (Field.toIsField X.functionField)

/-- The field structure on the rational functions of an integral scheme. -/
instance (X : Scheme.{u}) [IsIntegral X] : Field (rationalFunctions X) :=
  (isField_rationalFunctions X).toField

end Stacks.Chow
