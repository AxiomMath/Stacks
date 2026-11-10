module

public import StacksFrontier.Deformation.FormalObject.DerivationOrbits
public import StacksFrontier.Deformation.FormalObject.RepresentableMorphism
public import StacksFrontier.Deformation.FormalObject.VersalLifting
public import StacksFrontier.Deformation.FormalObject.YonedaEquivalence
public import StacksFrontier.Deformation.Formal.Groupoid.Prorepresentable
public import StacksFrontier.Deformation.GroupoidQuotient.TangentSpace
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Tangent
public import StacksFrontier.Deformation.Minimality
public import StacksFrontier.Deformation.PredeformationTangent.DerivationMap
public import StacksFrontier.Deformation.RimSchlessingerCategory.Prorepresentable
public import StacksFrontier.Deformation.Smooth.Basic
public import StacksFrontier.Deformation.TangentSpace.Derivations
public import StacksFrontier.Deformation.TangentSpace.SquareZero
public import StacksFrontier.Deformation.VersalObject.MinimalVersalOrbitBijection

/-!
# Tangent-space criteria for normalized and minimal groupoids in functors

Let `(U, R, s, t, c)` be a groupoid in functors on the category of Artinian local
`Λ`-algebras. Its quotient `[U/R]` is the Grothendieck construction of the pointwise
groupoids, and the quotient morphism `U → [U/R]` induces a map on tangent spaces, namely
the map of fibrewise isomorphism classes over the dual numbers.

Normalizedness of the groupoid -- its evaluation on the dual numbers has no arrows between
distinct objects -- says exactly that this differential is bijective. For a smooth
prorepresentable groupoid, minimality -- the quotient morphism is the morphism associated to
a minimal versal formal object -- says exactly that the kernel of the differential is
contained in the image of the canonical map `Der_Λ(k, k) → TU`.

## Main definitions

* `Deformation.GroupoidInFunctors.quotientDifferential` is the map induced by the quotient
  morphism `U → [U/R]` on tangent spaces.

## Main results

* `Deformation.GroupoidInFunctors.isNormalized_iff_bijective_quotientDifferential`: a groupoid
  in functors is normalized if and only if the differential is bijective.
* `Deformation.GroupoidInFunctors.isMinimal_iff_quotientDifferential_ker_le_derivationRange`: a
  smooth prorepresentable groupoid in functors is minimal if and only if the kernel of the
  differential is contained in the image of `Der_Λ(k, k) → TU`.
* `Deformation.GroupoidInFunctors.isNormalized_of_isMinimal_of_derivation_eq_zero`: a minimal
  smooth prorepresentable groupoid in functors is normalized as soon as the residue field
  carries no nonzero `Λ`-derivation.
* `Deformation.exists_isDerivationMorphism`: every derivation of the residue field is
  represented by a morphism from the residue field to the dual numbers.
* `Deformation.derivationToTangentSpace_elements` computes the canonical map
  `Der_Λ(k, k) → T𝓕` of Tag 06SV for a category of elements, on a point of the special
  fibre and a morphism representing the derivation.
* `Deformation.GroupoidInFunctors.isDeformationFunctor_objects_of_isProrepresentable` and
  `Deformation.GroupoidInFunctors.isDeformationFunctor_arrows_of_isProrepresentable`: the
  functors of objects and of arrows of a prorepresentable groupoid in functors are deformation
  functors.

## Implementation notes

Tangent spaces are the values over the dual numbers of the functors of fibrewise
isomorphism classes, so the differential is `Deformation.mapIsomorphismClasses` applied to
the quotient morphism; this is `Deformation.differential` of Tag 06II, with the two sides in
the universes natural for a groupoid in functors.

Part (1) needs neither smoothness nor prorepresentability, and is stated for an arbitrary
groupoid in functors.

The kernel of the differential is expressed as the set of tangent vectors with the same image
as the vector attached to the zero derivation, and the image of `Der_Λ(k, k)` as the range of
the canonical map of Tag 06SV, without fixing `k`-vector space structures on the two tangent
spaces.

Part (2) uses that `[U/R]` is a deformation category satisfying Schlessinger's condition (S2),
by Tag 06KU and Tag 06KT. The `IsNoetherianRing` and `Module.Finite` assumptions are the
standing hypotheses on `Λ → k` that define `𝒞_Λ` in Tag 06GC.

## References

* [Stacks Project, Tag 06KN](https://stacks.math.columbia.edu/tag/06KN)
* [Stacks Project, Tag 06KM](https://stacks.math.columbia.edu/tag/06KM)
* [Stacks Project, Tag 06KU](https://stacks.math.columbia.edu/tag/06KU)
* [Stacks Project, Tag 06T8](https://stacks.math.columbia.edu/tag/06T8)
-/

@[expose] public section

namespace Deformation

/-! ### Points of a category of elements under a morphism over the base -/

section
open CategoryTheory

universe u₁ v₁ w₁ w₂

/-- Transporting a point along an equality of objects commutes with pushing it forward. -/
private theorem map_eqToHom_comp {C : Type u₁} [Category.{v₁} C]
    (F : C ⥤ Type w₁) {A A' B B' : C} (hA : A = A') (hB : B = B')
    (f : A' ⟶ B') (x : F.obj A) :
    F.map (eqToHom hB) (F.map (eqToHom hA ≫ f ≫ eqToHom hB.symm) x) =
      F.map f (F.map (eqToHom hA) x) := by
  cases hA
  cases hB
  simp

/-- The identity factors through an equality of objects and its inverse. -/
private theorem id_eq_eqToHom_symm_comp {C : Type u₁} [Category.{v₁} C]
    {A B : C} (h : A = B) : 𝟙 B = eqToHom h.symm ≫ eqToHom h ≫ 𝟙 B := by
  cases h
  simp

/-- Two points become equal after transport precisely when the composite transport carries one
to the other. -/
private theorem map_eqToHom_comp_eqToHom_symm {C : Type u₁} [Category.{v₁} C]
    (H : C ⥤ Type w₂) {P Q P' : C} (h : P = Q) (h' : P' = Q)
    {z : H.obj P} {z' : H.obj P'}
    (hz : H.map (eqToHom h) z = H.map (eqToHom h') z') :
    H.map (eqToHom h ≫ eqToHom h'.symm) z = z' := by
  subst h
  subst h'
  simpa using hz

/-- An equality of objects composed with another one, read as a morphism through the common
object, is unchanged by inserting the identity. -/
private theorem eqToHom_comp_eq_id_comp {C : Type u₁} [Category.{v₁} C] {P Q A : C}
    (h : P = A) (h' : Q = A) :
    eqToHom h ≫ eqToHom h'.symm = eqToHom h ≫ 𝟙 A ≫ eqToHom h'.symm := by
  rw [Category.id_comp]

/-- Pushing a point forward along an equality of objects and then along a morphism out of the
other object is the same as pushing it along the morphism directly. -/
private theorem map_eqToHom_cancel {C : Type u₁} [Category.{v₁} C]
    (H : C ⥤ Type w₂) {P Q A : C} (h : P = Q) (v : P ⟶ A) (z : H.obj P) :
    H.map (eqToHom h.symm ≫ v) (H.map (eqToHom h) z) = H.map v z := by
  cases h
  simp

/-- The point of `H` over `A` determined by the image of a point of `F` over `A` under a
morphism of categories of elements over the base. The image object lies over `A` only up to
the structural equality, so its underlying point is transported along that equality. -/
private def elementsPointMap {C : Type u₁} [Category.{v₁} C]
    {F : C ⥤ Type w₁} {H : C ⥤ Type w₂}
    (φ : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π F))
      (BasedCategory.ofFunctor (Functor.Elements.π H)))
    (A : C) (x : F.obj A) : H.obj A :=
  H.map (eqToHom (φ.w_obj (F.elementsMk A x))) (φ.obj (F.elementsMk A x)).val

/-- The image object is isomorphic, over the identity of `A`, to the object of the category of
elements of `H` given by `elementsPointMap`. -/
private def elementsPointIso {C : Type u₁} [Category.{v₁} C]
    {F : C ⥤ Type w₁} {H : C ⥤ Type w₂}
    (φ : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π F))
      (BasedCategory.ofFunctor (Functor.Elements.π H)))
    (A : C) (x : F.obj A) :
    φ.obj (F.elementsMk A x) ≅ H.elementsMk A (elementsPointMap φ A x) :=
  Functor.Elements.isoMk (eqToIso (φ.w_obj (F.elementsMk A x))) rfl

/-- `elementsPointMap` is a natural transformation of set-valued functors. -/
private theorem elementsPointMap_naturality {C : Type u₁} [Category.{v₁} C]
    {F : C ⥤ Type w₁} {H : C ⥤ Type w₂}
    (φ : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π F))
      (BasedCategory.ofFunctor (Functor.Elements.π H)))
    {A B : C} (f : A ⟶ B) (x : F.obj A) :
    elementsPointMap φ B (F.map f x) = H.map f (elementsPointMap φ A x) := by
  let a := Functor.Elements.homMk (x := F.elementsMk A x) (y := F.elementsMk B (F.map f x)) f rfl
  have hb : (φ.map a).hom =
      eqToHom (φ.w_obj (F.elementsMk A x)) ≫ f ≫
        eqToHom (φ.w_obj (F.elementsMk B (F.map f x))).symm := by
    let : (BasedCategory.ofFunctor (Functor.Elements.π F)).p.IsHomLift f a :=
      IsHomLift.map (p := Functor.Elements.π F) a
    let : (Functor.Elements.π H).IsHomLift f (φ.map a) :=
      BasedFunctor.preserves_isHomLift φ f a
    exact IsHomLift.fac' (Functor.Elements.π H) f (φ.map a)
  dsimp only [elementsPointMap]
  rw [← (φ.map a).map_val, hb]
  exact map_eqToHom_comp H (φ.w_obj (F.elementsMk A x))
    (φ.w_obj (F.elementsMk B (F.map f x))) f (φ.obj (F.elementsMk A x)).val

/-- A full morphism of categories of elements over the base is injective on points. -/
private theorem elementsPointMap_injective {C : Type u₁} [Category.{v₁} C]
    {F : C ⥤ Type w₁} {H : C ⥤ Type w₂}
    (φ : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π F))
      (BasedCategory.ofFunctor (Functor.Elements.π H)))
    [φ.toFunctor.Full] (A : C) : Function.Injective (elementsPointMap φ A) := by
  intro x y hxy
  have hv : H.map (eqToHom (φ.w_obj (F.elementsMk A x)) ≫
        eqToHom (φ.w_obj (F.elementsMk A y)).symm)
      (φ.obj (F.elementsMk A x)).val = (φ.obj (F.elementsMk A y)).val :=
    map_eqToHom_comp_eqToHom_symm H (φ.w_obj (F.elementsMk A x))
      (φ.w_obj (F.elementsMk A y)) hxy
  let b : φ.obj (F.elementsMk A x) ⟶ φ.obj (F.elementsMk A y) :=
    Functor.Elements.homMk (eqToHom (φ.w_obj (F.elementsMk A x)) ≫
      eqToHom (φ.w_obj (F.elementsMk A y)).symm) hv
  have hb : (Functor.Elements.π H).IsHomLift (𝟙 A) b :=
    IsHomLift.of_fac' (Functor.Elements.π H) (𝟙 A) b
      (φ.w_obj (F.elementsMk A x)) (φ.w_obj (F.elementsMk A y))
      (eqToHom_comp_eq_id_comp (φ.w_obj (F.elementsMk A x))
        (φ.w_obj (F.elementsMk A y)))
  obtain ⟨c, hc⟩ := φ.toFunctor.map_surjective b
  have hlift : (Functor.Elements.π F).IsHomLift (𝟙 A) c := by
    let : (BasedCategory.ofFunctor (Functor.Elements.π H)).p.IsHomLift (𝟙 A)
        (φ.toFunctor.map c) := hc ▸ hb
    exact BasedFunctor.isHomLift_map φ (𝟙 A) c
  let := hlift
  have hcv : c.hom = 𝟙 A := by
    have h := IsHomLift.fac' (Functor.Elements.π F) (𝟙 A) c
    simpa [Functor.Elements.π] using h
  simpa [hcv] using c.map_val

/-- An essentially surjective morphism of categories of elements over the base is surjective
on points. -/
private theorem elementsPointMap_surjective {C : Type u₁} [Category.{v₁} C]
    {F : C ⥤ Type w₁} {H : C ⥤ Type w₂}
    (φ : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π F))
      (BasedCategory.ofFunctor (Functor.Elements.π H)))
    [φ.toFunctor.EssSurj] (A : C) : Function.Surjective (elementsPointMap φ A) := by
  intro y
  let Y := H.elementsMk A y
  let X := φ.toFunctor.objPreimage Y
  let i := φ.toFunctor.objObjPreimageIso Y
  refine ⟨F.map (eqToHom (φ.w_obj X).symm ≫ i.hom.hom) X.val, ?_⟩
  exact (elementsPointMap_naturality φ (eqToHom (φ.w_obj X).symm ≫ i.hom.hom) X.val).trans
    ((map_eqToHom_cancel H (φ.w_obj X) i.hom.hom (φ.obj X).val).trans i.hom.map_val)

/-- Objects of a fibre joined by an arrow lifting the identity have the same class. -/
private theorem classOf_eq_of_homLift {C : Type*} [Category C]
    {F : Type*} [Category F] (p : F ⥤ C) (hp : IsCofiberedInGroupoids p) {A : C}
    (x y : p.Fiber A) (f : x.1 ⟶ y.1) (hf : p.IsHomLift (𝟙 A) f) :
    classOf (BasedCategory.ofFunctor p) hp x =
      classOf (BasedCategory.ofFunctor p) hp y := by
  let : (BasedCategory.ofFunctor p).p.IsHomLift (𝟙 A) f := hf
  simpa using map_classOf (BasedCategory.ofFunctor p) hp (𝟙 A) x y f

end

/-! ### Smoothness is invariant under isomorphism of morphisms over the base -/

section
open CategoryTheory

universe u v w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A morphism over `𝒞_Λ` isomorphic to a smooth one is smooth. -/
private theorem isSmooth_of_basedIso
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    {φ ψ : BasedFunctor 𝓕 𝓖} (i : φ ≅ ψ) (hφ : IsSmooth φ) : IsSmooth ψ := by
  intro B A f hf y x g hg
  have hA : 𝓕.p.obj x = A := (ψ.w_obj x).symm.trans (IsHomLift.codomain_eq 𝓖.p f g)
  have hi : 𝓖.p.IsHomLift (𝟙 A) (i.inv.app x) := hA ▸ i.inv.isHomLift' x
  let := hg
  let := hi
  have hg' : 𝓖.p.IsHomLift f (g ≫ i.inv.app x) := by
    simpa using IsHomLift.comp 𝓖.p f (𝟙 A) g (i.inv.app x)
  obtain ⟨x', h, a, hh, ha, hfac⟩ := hφ f hf y x (g ≫ i.inv.app x) hg'
  have hB : 𝓕.p.obj x' = B := IsHomLift.domain_eq 𝓕.p f h
  have hi' : 𝓖.p.IsHomLift (𝟙 B) (i.inv.app x') := hB ▸ i.inv.isHomLift' x'
  refine ⟨x', h, i.inv.app x' ≫ a, hh, ?_, ?_⟩
  · let := hi'
    let := ha
    simpa using IsHomLift.comp 𝓖.p (𝟙 B) (𝟙 B) (i.inv.app x') a
  · apply (cancel_mono (i.inv.app x)).mp
    simp only [Category.assoc] at *
    rw [← hfac]
    exact i.inv.naturality h

end

/-! ### Morphisms of `𝒞_Λ` representing derivations of the residue field -/

section
open CategoryTheory

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Every derivation of the residue field is represented by a morphism of `𝒞_Λ` from the
residue field to the dual numbers. -/
public theorem exists_isDerivationMorphism (D : Derivation Λ k k) :
    ∃ f : residueFieldObject.{u, v, w} Λ k ⟶ artinianDualNumbers.{u, w, v} Λ k,
      IsDerivationMorphism D f :=
  ⟨derivationMorphism D, derivationMorphism_isDerivationMorphism D⟩

/-- The derivation of a complete local algebra attached to one of its tangent vectors, as a
derivation into the residue field with the module structure used by `Deformation.Derivations`. -/
private noncomputable def pointDerivation
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    (α : (restrictedCoyoneda R).obj (artinianDualNumbers.{u, w, v} Λ k)) :
    Derivations R k := by
  letI : Algebra R k := (residueHom R).toRingHom.toAlgebra
  let D := tangentSpaceDerivationsLinearEquiv R α
  have hadd := D.map_add
  have hone := D.map_one_eq_zero
  have hsmul (a : Λ) (r : R) : D (a • r) = algebraMap Λ k a * D r := by
    rw [← Algebra.smul_def]
    exact D.map_smul a r
  have hmul (r s : R) :
      D (r * s) = residueHom R r * D s + residueHom R s * D r := D.leibniz r s
  let d : R → k := D
  letI : Module Λ k := Module.compHom k (algebraMap Λ k)
  letI : Module R k := Module.compHom k (residueHom R).toRingHom
  exact
    { toFun := d
      map_add' := hadd
      map_smul' := hsmul
      map_one_eq_zero' := hone
      leibniz' := hmul }

/-- The derivation attached to a tangent vector is its square-zero coordinate. -/
private theorem pointDerivation_apply
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    (α : (restrictedCoyoneda R).obj (artinianDualNumbers.{u, w, v} Λ k))
    (r : R) : pointDerivation R α r = (α.hom r).snd.down :=
  tangentSpaceDerivationsLinearEquiv_apply R α r

/-- Two tangent vectors of a complete local algebra with the same square-zero coordinates are
equal. -/
private theorem tangentVector_ext {R : CompleteLocalAlgCat.{u, max v w, w} Λ k}
    {a b : (restrictedCoyoneda R).obj (artinianDualNumbers.{u, w, v} Λ k)}
    (h : ∀ r : R, (a.hom r).snd.down = (b.hom r).snd.down) : a = b := by
  apply CompleteLocalAlgCat.Hom.ext
  apply AlgHom.ext
  intro r
  apply TrivSqZeroExt.ext
  · exact (a.residue_comm r).trans (b.residue_comm r).symm
  · exact ULift.ext (h r)

end

/-! ### Classes of the points of the morphism associated to a formal object -/

section
open CategoryTheory

universe u v w q r

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type q} [Category.{r} F]

/-- The equivalence of categories of elements induced by an isomorphism of set-valued
functors. -/
private noncomputable def elementsEquivOfNatIso
    {C : Type q} [Category.{r} C] {F H : C ⥤ Type w} (i : F ≅ H) :
    F.Elements ≌ H.Elements where
  functor := NatTrans.mapElements i.hom
  inverse := NatTrans.mapElements i.inv
  unitIso := NatIso.ofComponents (fun X => Functor.Elements.isoMk (Iso.refl _)
    (by simp [NatTrans.mapElements]))
    (by intros; ext; simp [NatTrans.mapElements, Functor.Elements.isoMk])
  counitIso := NatIso.ofComponents (fun X => Functor.Elements.isoMk (Iso.refl _)
    (by simp [NatTrans.mapElements]))
    (by intros; ext; simp [NatTrans.mapElements, Functor.Elements.isoMk])
  functor_unitIso_comp X := by ext; simp [NatTrans.mapElements, Functor.Elements.isoMk]

/-- The canonical arrow from the selected level of a formal object to the value of its
associated morphism at an Artinian point lies over the inducing map. -/
private theorem associatedPointInclusion_isHomLift
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (ξ : FormalObject p) (P : ChosenPushforwards p) (M : AssociatedMorphism ξ P)
    (a : (restrictedCoyoneda ξ.base).Elements) :
    p.IsHomLift (M.factor a) (M.pointInclusion a) := by
  apply (IsHomLift.eqToHom_comp_lift_iff p (M.factor a)
    (M.pointInclusion a) (M.obj_eq a)).1
  rw [M.pointInclusion_eq]
  let := (P (M.factor a)).cocartesian ⟨ξ.level (M.level a), ξ.level_eq (M.level a)⟩
  infer_instance

/-- The adic truncation functor acts on residue classes by acting on representatives. -/
private theorem truncationMap_apply_mk
    {R S : CompleteLocalAlgCat.{u, max v w, w} Λ k} (f : R ⟶ S) (n : ℕ) (r : R) :
    ((AdicTruncation.functor n).map f).hom
        (Ideal.Quotient.mk (AdicTruncation.ideal R n) r) =
      Ideal.Quotient.mk (AdicTruncation.ideal S n) (f.hom r) := rfl

/-- Transporting a residue class along an equality of truncation levels keeps the
representative. -/
private theorem truncationEqToHom_apply_mk
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) {n m : ℕ} (h : n = m) (r : R) :
    (eqToHom (congrArg (AdicTruncation.obj R) h)).hom
        (Ideal.Quotient.mk (AdicTruncation.ideal R n) r) =
      Ideal.Quotient.mk (AdicTruncation.ideal R m) r := by
  cases h
  rfl

/-- A map out of an adic truncation, precomposed with the truncation of a morphism of complete
local algebras, acts on a residue class through its representative. -/
private theorem truncation_comp_apply_mk
    {R S : CompleteLocalAlgCat.{u, max v w, w} Λ k}
    {T : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : R ⟶ S) (n : ℕ)
    (g : AdicTruncation.obj S n ⟶ T) (r : R) :
    ((AdicTruncation.functor n).map f ≫ g).hom
        (Ideal.Quotient.mk (AdicTruncation.ideal R n) r) =
      g.hom (Ideal.Quotient.mk (AdicTruncation.ideal S n) (f.hom r)) := rfl

/-- A map out of an adic truncation, precomposed with a transport along an equality of levels,
acts on a residue class through its representative. -/
private theorem eqToHom_comp_apply_mk
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    {T : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {n m : ℕ} (h : n = m)
    (g : AdicTruncation.obj R m ⟶ T) (r : R) :
    (eqToHom (congrArg (AdicTruncation.obj R) h) ≫ g).hom
        (Ideal.Quotient.mk (AdicTruncation.ideal R n) r) =
      g.hom (Ideal.Quotient.mk (AdicTruncation.ideal R m) r) := by
  cases h
  rfl

/-- The classes of the levels of a formal object are compatible with equalities of levels. -/
private theorem formalLevelClass_transport
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) {n m : ℕ} (h : n = m) :
    (isomorphismClasses (BasedCategory.ofFunctor p) hp).map
        (eqToHom (congrArg (AdicTruncation.obj ξ.base) h))
        (classOf (BasedCategory.ofFunctor p) hp ⟨ξ.level n, ξ.level_eq n⟩) =
      classOf (BasedCategory.ofFunctor p) hp ⟨ξ.level m, ξ.level_eq m⟩ := by
  cases h
  exact Functor.map_id_apply _ _ _

/-- Two Artinian points of the base of a formal object that agree after precomposition with a
morphism of formal objects have the same class under the associated morphism. -/
private theorem associatedPointClass_eq_of_base_precomp_eq
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    {ξ η : FormalObject p} (θ : η ⟶ ξ) (P : ChosenPushforwards p)
    (T : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (a b : (restrictedCoyoneda ξ.base).obj T) (hab : θ.base ≫ a = θ.base ≫ b) :
    let M := associatedMorphism hp ξ P
    classOf (BasedCategory.ofFunctor p) hp
        ⟨M.toBasedFunctor.obj ⟨a⟩, M.toBasedFunctor.w_obj ⟨a⟩⟩ =
      classOf (BasedCategory.ofFunctor p) hp
        ⟨M.toBasedFunctor.obj ⟨b⟩, M.toBasedFunctor.w_obj ⟨b⟩⟩ := by
  let M := associatedMorphism hp ξ P
  let A := (restrictedCoyoneda ξ.base).elementsMk T a
  let B := (restrictedCoyoneda ξ.base).elementsMk T b
  have hn : M.level A = M.level B :=
    Nat.le_antisymm ((M.factor_spec A).2.1 (M.level B) (M.factor_spec B).1)
      ((M.factor_spec B).2.1 (M.level A) (M.factor_spec A).1)
  have hpt (s : η.base) :
      (M.factor A).hom (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base (M.level A))
          (θ.base.hom s)) =
        (M.factor B).hom (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base (M.level B))
          (θ.base.hom s)) := by
    have ha := congrArg (fun f : ξ.base →ₐ[Λ] T => f (θ.base.hom s))
      (M.factor_spec A).2.2
    have hb := congrArg (fun f : ξ.base →ₐ[Λ] T => f (θ.base.hom s))
      (M.factor_spec B).2.2
    dsimp only [AlgHom.comp_apply] at ha hb
    have h : a.hom (θ.base.hom s) = b.hom (θ.base.hom s) :=
      congrArg (fun f : η.base ⟶ artinianToComplete.obj T => f.hom s) hab
    exact ha.trans (h.trans hb.symm)
  have hde : (AdicTruncation.functor (M.level A)).map θ.base ≫ M.factor A =
      eqToHom (congrArg (AdicTruncation.obj η.base) hn) ≫
        ((AdicTruncation.functor (M.level B)).map θ.base ≫ M.factor B) := by
    apply ArtinianLocalAlgCat.Hom.ext
    apply AlgHom.ext
    intro x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [truncation_comp_apply_mk θ.base (M.level A) (M.factor A) s,
      eqToHom_comp_apply_mk η.base hn
        ((AdicTruncation.functor (M.level B)).map θ.base ≫ M.factor B) s,
      truncation_comp_apply_mk θ.base (M.level B) (M.factor B) s]
    exact hpt s
  have hca : p.IsHomLift ((AdicTruncation.functor (M.level A)).map θ.base ≫ M.factor A)
      (θ.app (M.level A) ≫ M.pointInclusion A) := by
    let := θ.app_lift (M.level A)
    let := associatedPointInclusion_isHomLift ξ P M A
    exact IsHomLift.comp p _ _ _ _
  have hcb : p.IsHomLift ((AdicTruncation.functor (M.level B)).map θ.base ≫ M.factor B)
      (θ.app (M.level B) ≫ M.pointInclusion B) := by
    let := θ.app_lift (M.level B)
    let := associatedPointInclusion_isHomLift ξ P M B
    exact IsHomLift.comp p _ _ _ _
  have hya := @map_classOf _ _ (BasedCategory.ofFunctor p) hp _ T
    ((AdicTruncation.functor (M.level A)).map θ.base ≫ M.factor A)
    ⟨η.level (M.level A), η.level_eq (M.level A)⟩
    ⟨M.toBasedFunctor.obj A, M.toBasedFunctor.w_obj A⟩
    (θ.app (M.level A) ≫ M.pointInclusion A) hca
  have hyb := @map_classOf _ _ (BasedCategory.ofFunctor p) hp _ T
    ((AdicTruncation.functor (M.level B)).map θ.base ≫ M.factor B)
    ⟨η.level (M.level B), η.level_eq (M.level B)⟩
    ⟨M.toBasedFunctor.obj B, M.toBasedFunctor.w_obj B⟩
    (θ.app (M.level B) ≫ M.pointInclusion B) hcb
  refine hya.symm.trans (Eq.trans ?_ hyb)
  rw [hde, Functor.map_comp_apply, formalLevelClass_transport hp η hn]

/-- The class of the value of the associated morphism at a tangent vector of the base is
related to the derivation of that tangent vector by the differential. -/
private theorem derivationDifferentialGraph_of_point
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) (ξ : FormalObject p) (P : ChosenPushforwards p)
    (α : (restrictedCoyoneda ξ.base).obj (artinianDualNumbers.{u, w, v} Λ k)) :
    derivationDifferentialGraph.{u, v, w} p hp ξ (pointDerivation ξ.base α)
      (classOf (BasedCategory.ofFunctor p) hp.cofibered
        ⟨(associatedMorphism hp.cofibered ξ P).toBasedFunctor.obj ⟨α⟩,
          (associatedMorphism hp.cofibered ξ P).toBasedFunctor.w_obj ⟨α⟩⟩) :=
  ⟨P, α, fun s => (pointDerivation_apply ξ.base α s).symm,
    mapIsomorphismClasses_classOf _ _ _ _⟩

/-- Two points of the base of a minimal versal formal object with the same class under the
associated morphism differ by a derivation of the residue field. -/
private theorem exists_derivation_of_associatedPointClass_eq
    [IsNoetherianRing Λ] [Module.Finite Λ k] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p) (hS2 : SchlessingerConditionS2 p) (ξ : FormalObject p)
    (hmin : IsMinimalVersal hp.cofibered ξ) (P : ChosenPushforwards p)
    (a b : (restrictedCoyoneda ξ.base).obj (artinianDualNumbers.{u, w, v} Λ k))
    (h : classOf (BasedCategory.ofFunctor p) hp.cofibered
          ⟨(associatedMorphism hp.cofibered ξ P).toBasedFunctor.obj ⟨a⟩,
            (associatedMorphism hp.cofibered ξ P).toBasedFunctor.w_obj ⟨a⟩⟩ =
        classOf (BasedCategory.ofFunctor p) hp.cofibered
          ⟨(associatedMorphism hp.cofibered ξ P).toBasedFunctor.obj ⟨b⟩,
            (associatedMorphism hp.cofibered ξ P).toBasedFunctor.w_obj ⟨b⟩⟩) :
    ∃ δ : Derivation Λ k k, ∀ r : ξ.base,
      pointDerivation ξ.base a r = pointDerivation ξ.base b r + δ (residueHom ξ.base r) :=
  ((minimalVersal_hasBijectiveDifferentialOnDerivationOrbits.{u, v, w} p hp hS2 ξ
    hmin).2.2.2 (pointDerivation ξ.base b) (pointDerivation ξ.base a) _ _
    (derivationDifferentialGraph_of_point p hp ξ P b)
    (derivationDifferentialGraph_of_point p hp ξ P a)).1
    ⟨0, h.trans ((derivationAction.{u, v, w} p hp).zero_action _).symm⟩

/-- A versal formal object whose differential has no kernel beyond the derivations of the
residue field is minimal. -/
private theorem isMinimalVersal_of_tangentKernel
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) (hξ : IsVersal hp ξ)
    (P : ChosenPushforwards p)
    (hkernel : ∀ a b : (restrictedCoyoneda ξ.base).obj (artinianDualNumbers.{u, w, v} Λ k),
      (∀ r : ξ.base, (b.hom r).snd.down = 0) →
      (let M := associatedMorphism hp ξ P
       classOf (BasedCategory.ofFunctor p) hp
          ⟨M.toBasedFunctor.obj ⟨a⟩, M.toBasedFunctor.w_obj ⟨a⟩⟩ =
        classOf (BasedCategory.ofFunctor p) hp
          ⟨M.toBasedFunctor.obj ⟨b⟩, M.toBasedFunctor.w_obj ⟨b⟩⟩) →
      ∃ δ : Derivation Λ k k, ∀ r : ξ.base,
        (a.hom r).snd.down = δ (residueHom ξ.base r)) :
    IsMinimalVersal hp ξ := by
  refine ⟨hξ, fun η θ => surjective_of_residueDerivation_comap_injective θ.base ?_⟩
  let : Algebra ξ.base k := (residueAlgHom ξ.base).toRingHom.toAlgebra
  let e := tangentSpaceDerivationsLinearEquiv ξ.base
  intro D E hDE
  have hDE' (r : η.base) : D (θ.base.hom r) = E (θ.base.hom r) :=
    congrArg (fun d => d r) hDE
  let a := e.symm (D - E)
  let b := e.symm 0
  have ha (r : ξ.base) : (a.hom r).snd.down = D r - E r :=
    (tangentSpaceDerivationsLinearEquiv_apply ξ.base a r).symm.trans
      (congrArg (fun d => d r) (e.apply_symm_apply (D - E)))
  have hb (r : ξ.base) : (b.hom r).snd.down = 0 :=
    (tangentSpaceDerivationsLinearEquiv_apply ξ.base b r).symm.trans
      (congrArg (fun d => d r) (e.apply_symm_apply 0))
  have hpre : θ.base ≫ a = θ.base ≫ b := by
    refine tangentVector_ext fun r => ?_
    change (a.hom (θ.base.hom r)).snd.down = (b.hom (θ.base.hom r)).snd.down
    rw [ha, hb]
    exact sub_eq_zero.mpr (hDE' r)
  obtain ⟨δ, hδ⟩ := hkernel a b hb
    (associatedPointClass_eq_of_base_precomp_eq hp θ P _ a b hpre)
  have hδzero (x : k) : δ x = 0 := by
    obtain ⟨r₀, hr₀⟩ := η.base.residueEquiv.surjective x
    obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective r₀
    have hx : residueHom ξ.base (θ.base.hom r) = x :=
      (θ.base.residue_comm r).trans ((congrArg η.base.residueEquiv hr).trans hr₀)
    have hd := hδ (θ.base.hom r)
    rw [ha, hDE' r, sub_self, hx] at hd
    exact hd.symm
  apply Derivation.ext
  intro r
  have h := hδ r
  rw [ha, hδzero] at h
  exact sub_eq_zero.mp h

/-- A morphism over `𝒞_Λ` out of the category of elements of a prorepresentable functor is,
after transporting along the identification of that functor with a represented one, the
morphism associated to a formal object. -/
private theorem exists_associatedMorphism_presentation
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    (U : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type (max v w))
    (R : CompleteLocalAlgCat.{u, max v w, w} Λ k)
    (α : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda R)))
      (BasedCategory.ofFunctor p))
    (e : U.Elements ≌ (restrictedCoyoneda R).Elements)
    (he : e.functor ⋙ Functor.Elements.π (restrictedCoyoneda R) = Functor.Elements.π U)
    (P : ChosenPushforwards p) :
    ∃ (ξ : FormalObject p) (e' : U.Elements ≌ (restrictedCoyoneda ξ.base).Elements),
      (e'.functor ⋙ Functor.Elements.π (restrictedCoyoneda ξ.base) =
          Functor.Elements.π U) ∧
        Nonempty { i : e.functor ⋙ α.toFunctor ≅ e'.functor ⋙
          (associatedMorphism hp ξ P).toBasedFunctor.toFunctor //
            ∀ X : U.Elements, p.IsHomLift (𝟙 X.1) (i.hom.app X) } := by
  let E := representableMorphismFormalObjectEquivalence p hp R
  generalize hX : E.equivalence.functor.obj α = X
  obtain ⟨ξ, hbase⟩ := X
  change ξ.base = R at hbase
  subst R
  obtain ⟨j⟩ := associatedMorphism_maps_to hp ξ E P
  let i := E.equivalence.functor.preimageIso ((eqToIso hX) ≪≫ j.symm)
  let φ := (associatedMorphism hp ξ P).toBasedFunctor
  let i' : α.toFunctor ≅ φ.toFunctor :=
    { hom := i.hom.toNatTrans
      inv := i.inv.toNatTrans
      hom_inv_id := congrArg (fun f => f.toNatTrans) i.hom_inv_id
      inv_hom_id := congrArg (fun f => f.toNatTrans) i.inv_hom_id }
  let β : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π U))
      (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda ξ.base))) :=
    ⟨e.functor, he⟩
  exact ⟨ξ, e, he, ⟨⟨Functor.isoWhiskerLeft e.functor i',
    fun X => (BasedCategory.whiskerLeft β i.hom).isHomLift' X⟩⟩⟩

end

/-! ### The differential of the quotient morphism -/

section
open CategoryTheory

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Two objects of a fibre have the same class in the associated functor of fibrewise
isomorphism classes precisely when they have the same class in the fibrewise isomorphism
quotient. -/
public theorem classOf_eq_iff_quotient_mk_eq {C : Type*} [Category C]
    (𝓕 : BasedCategory C) (h𝓕 : IsCofiberedInGroupoids 𝓕.p) {A : C}
    (x y : Functor.Fiber 𝓕.p A) :
    classOf 𝓕 h𝓕 x = classOf 𝓕 h𝓕 y ↔
      Quotient.mk (isIsomorphicSetoid (Functor.Fiber 𝓕.p A)) x =
        Quotient.mk (isIsomorphicSetoid (Functor.Fiber 𝓕.p A)) y := by
  refine ⟨fun h => ?_, fun h => classOf_eq_of_isIsomorphic 𝓕 h𝓕 x y (Quotient.exact h)⟩
  calc
    _ = cast (isomorphismClasses_obj 𝓕 h𝓕 A) (classOf 𝓕 h𝓕 x) :=
          (classOf_eq 𝓕 h𝓕 x).symm
    _ = cast (isomorphismClasses_obj 𝓕 h𝓕 A) (classOf 𝓕 h𝓕 y) := congrArg _ h
    _ = _ := classOf_eq 𝓕 h𝓕 y

/-- Two objects of a fibre of a category of elements with the same isomorphism class in the
associated functor are equal: such a fibre is discrete. -/
public theorem classOf_objectFiber_injective
    {C : Type*} [Category C] (F : C ⥤ Type*) (A : C) :
    Function.Injective (fun x : F.obj A =>
      classOf (BasedCategory.ofFunctor (Functor.Elements.π F))
        (categoryOfElements_projection_isCofibered F) (objectFiber A x)) := by
  intro x y hxy
  have hiso : IsIsomorphic (objectFiber A x) (objectFiber A y) :=
    Quotient.exact ((classOf_eq_iff_quotient_mk_eq _
      (categoryOfElements_projection_isCofibered F) _ _).1 hxy)
  have h2 : F.elementsMk A x = F.elementsMk A y :=
    congrArg Subtype.val (elementsFiber_skeletal F A hiso)
  simpa using h2

/-- The canonical map from derivations of the residue field, computed on a point of the
special fibre and a morphism representing the derivation. -/
public theorem derivationToTangentSpace_elements
    (F : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type (max v w))
    (hF : IsPredeformationCategory (Functor.Elements.π F))
    (D : Derivation Λ k k) (x₀ : F.obj (residueFieldObject.{u, v, w} Λ k))
    (f : residueFieldObject.{u, v, w} Λ k ⟶ artinianDualNumbers.{u, w, v} Λ k)
    (hf : IsDerivationMorphism D f) :
    derivationToTangentSpace (Functor.Elements.π F) hF D =
      classOf (BasedCategory.ofFunctor (Functor.Elements.π F)) hF.cofibered
        (objectFiber (artinianDualNumbers.{u, w, v} Λ k) (F.map f x₀)) := by
  rw [derivationToTangentSpace_apply (Functor.Elements.π F) hF D
    (objectFiber (residueFieldObject.{u, v, w} Λ k) x₀) f hf]
  let a := Functor.Elements.homMk (x := F.elementsMk (residueFieldObject.{u, v, w} Λ k) x₀)
    (y := F.elementsMk (artinianDualNumbers.{u, w, v} Λ k) (F.map f x₀)) f rfl
  exact @map_classOf _ _ (BasedCategory.ofFunctor (Functor.Elements.π F)) hF.cofibered
    _ _ f (objectFiber (residueFieldObject.{u, v, w} Λ k) x₀)
    (objectFiber (artinianDualNumbers.{u, w, v} Λ k) (F.map f x₀)) a
    (IsHomLift.map (p := Functor.Elements.π F) a)

namespace GroupoidInFunctors

/-- The map induced on tangent spaces by the quotient morphism `U → [U/R]`. -/
public noncomputable def quotientDifferential
    (G : GroupoidInFunctors (ArtinianLocalAlgCat.{u, max v w, w} Λ k)) :
    tangentSpaceArtinian.{u, w, v} Λ k
        (isomorphismClasses (BasedCategory.ofFunctor (Functor.Elements.π G.objects))
          (categoryOfElements_projection_isCofibered G.objects)) →
      tangentSpaceArtinian.{u, w, v} Λ k
        (isomorphismClasses (BasedCategory.ofFunctor
          (Grothendieck.forget (evaluationFunctor G))) (quotientProjection_cofibered G)) :=
  mapIsomorphismClasses (categoryOfElements_projection_isCofibered G.objects)
    (quotientProjection_cofibered G) (quotientBasedFunctor G)
    (artinianDualNumbers.{u, w, v} Λ k)

/-- The differential of the quotient morphism sends the class of a point of `U` to the class
of the corresponding object of the quotient. -/
public theorem quotientDifferential_classOf
    (G : GroupoidInFunctors (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (x : G.objects.obj (artinianDualNumbers.{u, w, v} Λ k)) :
    quotientDifferential.{u, v, w} G
        (classOf (BasedCategory.ofFunctor (Functor.Elements.π G.objects))
          (categoryOfElements_projection_isCofibered G.objects)
          (objectFiber (artinianDualNumbers.{u, w, v} Λ k) x)) =
      classOf (BasedCategory.ofFunctor (Grothendieck.forget (evaluationFunctor G)))
        (quotientProjection_cofibered G)
        (quotientFiberObject G (artinianDualNumbers.{u, w, v} Λ k) x) :=
  mapIsomorphismClasses_classOf (categoryOfElements_projection_isCofibered G.objects)
    (quotientProjection_cofibered G) (quotientBasedFunctor G)
    (objectFiber (artinianDualNumbers.{u, w, v} Λ k) x)

/-- The differential of the quotient morphism is surjective. -/
private theorem quotientDifferential_surjective
    (G : GroupoidInFunctors (ArtinianLocalAlgCat.{u, max v w, w} Λ k)) :
    Function.Surjective (quotientDifferential.{u, v, w} G) := by
  intro z
  obtain ⟨X, hX⟩ := classOf_surjective _ (quotientProjection_cofibered G)
    (artinianDualNumbers.{u, w, v} Λ k) z
  obtain ⟨x, rfl⟩ := quotientFiberObject_surjective G (artinianDualNumbers.{u, w, v} Λ k) X
  exact ⟨_, (quotientDifferential_classOf G x).trans hX⟩

/-- A groupoid in functors is normalized precisely when the quotient morphism `U → [U/R]` induces
an isomorphism on tangent spaces. -/
@[stacks 06KN "part (1): normalized iff isomorphism on tangent spaces"]
public theorem isNormalized_iff_bijective_quotientDifferential
    (G : GroupoidInFunctors (ArtinianLocalAlgCat.{u, max v w, w} Λ k)) :
    IsNormalized.{u, v, w} G ↔ Function.Bijective (quotientDifferential.{u, v, w} G) := by
  let T := artinianDualNumbers.{u, w, v} Λ k
  let 𝓤 := BasedCategory.ofFunctor (Functor.Elements.π G.objects)
  let h𝓤 := categoryOfElements_projection_isCofibered G.objects
  let 𝓠 := BasedCategory.ofFunctor (Grothendieck.forget (evaluationFunctor G))
  let h𝓠 := quotientProjection_cofibered G
  constructor
  · refine fun hnorm => ⟨fun a b hab => ?_, quotientDifferential_surjective G⟩
    obtain ⟨a, rfl⟩ := classOf_surjective 𝓤 h𝓤 T a
    obtain ⟨b, rfl⟩ := classOf_surjective 𝓤 h𝓤 T b
    obtain ⟨x, rfl⟩ := objectFiber_surjective T a
    obtain ⟨y, rfl⟩ := objectFiber_surjective T b
    have hcl : classOf 𝓠 h𝓠 (quotientFiberObject G T x) =
        classOf 𝓠 h𝓠 (quotientFiberObject G T y) := by
      rwa [← quotientDifferential_classOf G x, ← quotientDifferential_classOf G y]
    obtain ⟨i⟩ := (Quotient.exact ((classOf_eq_iff_quotient_mk_eq 𝓠 h𝓠 _ _).1 hcl) :
      Nonempty (quotientFiberObject G T x ≅ quotientFiberObject G T y))
    obtain ⟨r, hrs, hrt⟩ := arrowOfQuotientFiberHom G T i.hom
    exact congrArg (fun z : G.objects.obj T => classOf 𝓤 h𝓤 (objectFiber T z))
      (hrs.symm.trans ((hnorm r).trans hrt))
  · intro hbij a
    have hcl : classOf 𝓠 h𝓠 (quotientFiberObject G T (G.source.app T a)) =
        classOf 𝓠 h𝓠 (quotientFiberObject G T (G.target.app T a)) :=
      classOf_eq_of_isIsomorphic 𝓠 h𝓠 _ _ ⟨quotientFiberIsoOfArrow G T a rfl rfl⟩
    have hdiff : quotientDifferential.{u, v, w} G
          (classOf 𝓤 h𝓤 (objectFiber T (G.source.app T a))) =
        quotientDifferential.{u, v, w} G
          (classOf 𝓤 h𝓤 (objectFiber T (G.target.app T a))) := by
      rwa [quotientDifferential_classOf G, quotientDifferential_classOf G]
    exact classOf_objectFiber_injective G.objects T (hbij.1 hdiff)

end GroupoidInFunctors

end

/-! ### Minimality and the kernel of the differential -/

section
open CategoryTheory

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

namespace GroupoidInFunctors

variable (G : GroupoidInFunctors.{_, max v w, max v w}
  (ArtinianLocalAlgCat.{u, max v w, w} Λ k))

/-- The functor of objects of a prorepresentable groupoid in functors is a deformation
functor. -/
public theorem isDeformationFunctor_objects_of_isProrepresentable
    (hpro : IsProrepresentable G) : IsDeformationFunctor G.objects :=
  isDeformationFunctor_of_isProrepresentable G.objects
    ((isProrepresentable_iff_objects_arrows G).1 hpro).1

/-- The functor of arrows of a prorepresentable groupoid in functors is a deformation
functor. -/
public theorem isDeformationFunctor_arrows_of_isProrepresentable
    (hpro : IsProrepresentable G) : IsDeformationFunctor G.arrows :=
  isDeformationFunctor_of_isProrepresentable G.arrows
    ((isProrepresentable_iff_objects_arrows G).1 hpro).2

/-- The category of elements of the functor of objects of a prorepresentable groupoid in
functors is a predeformation category. -/
public theorem objects_isPredeformationCategory_of_isProrepresentable
    (hpro : IsProrepresentable G) :
    IsPredeformationCategory (Functor.Elements.π G.objects) :=
  ((isDeformationCategory_iff G.objects).2
    (isDeformationFunctor_objects_of_isProrepresentable G hpro)).predeformation

/-- The quotient of a prorepresentable groupoid in functors is a predeformation category. -/
public theorem quotient_isPredeformationCategory_of_isProrepresentable
    (hpro : IsProrepresentable G) :
    IsPredeformationCategory (Grothendieck.forget (evaluationFunctor G)) :=
  quotient_isPredeformationCategory G
    (isDeformationFunctor_objects_of_isProrepresentable G hpro)
    (isDeformationFunctor_arrows_of_isProrepresentable G hpro)

/-- The quotient of a smooth prorepresentable groupoid in functors satisfies Schlessinger's
condition (S2). -/
public theorem quotient_schlessingerConditionS2_of_isProrepresentable
    (hpro : IsProrepresentable G) (hsmooth : IsSmooth G) :
    SchlessingerConditionS2 (Grothendieck.forget (evaluationFunctor G)) :=
  schlessingerConditionS2_of_satisfiesRS (quotient_satisfiesRS G hsmooth
    (isDeformationFunctor_objects_of_isProrepresentable G hpro).2
    (isDeformationFunctor_arrows_of_isProrepresentable G hpro).2)

/-- When the quotient morphism is identified with the morphism associated to a formal object,
the class of a point of `U` in the quotient is the class of the value of that associated
morphism at the corresponding point of the represented functor. -/
private theorem quotientClass_eq_associatedPointClass
    (hp : IsPredeformationCategory (Grothendieck.forget (evaluationFunctor G)))
    (ξ : FormalObject (Grothendieck.forget (evaluationFunctor G)))
    (P : ChosenPushforwards (Grothendieck.forget (evaluationFunctor G)))
    (φ : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π G.objects))
      (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda ξ.base))))
    (i : quotientMorphism G ≅ φ.toFunctor ⋙
      (associatedMorphism hp.cofibered ξ P).toBasedFunctor.toFunctor)
    (hi : ∀ X : G.objects.Elements,
      (Grothendieck.forget (evaluationFunctor G)).IsHomLift (𝟙 X.1) (i.hom.app X))
    (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) (x : G.objects.obj A) :
    classOf (BasedCategory.ofFunctor (Grothendieck.forget (evaluationFunctor G)))
        hp.cofibered (quotientFiberObject G A x) =
      classOf (BasedCategory.ofFunctor (Grothendieck.forget (evaluationFunctor G)))
        hp.cofibered
        ⟨(associatedMorphism hp.cofibered ξ P).toBasedFunctor.obj
            ⟨elementsPointMap φ A x⟩,
          (associatedMorphism hp.cofibered ξ P).toBasedFunctor.w_obj
            ⟨elementsPointMap φ A x⟩⟩ := by
  let p := Grothendieck.forget (evaluationFunctor G)
  let ψ := (associatedMorphism hp.cofibered ξ P).toBasedFunctor
  let j := elementsPointIso φ A x
  have hj : (Functor.Elements.π (restrictedCoyoneda ξ.base)).IsHomLift (𝟙 A) j.hom :=
    IsHomLift.of_fac _ (𝟙 A) j.hom (φ.w_obj (G.objects.elementsMk A x)) rfl
      (id_eq_eqToHom_symm_comp (φ.w_obj (G.objects.elementsMk A x)))
  have hψj : p.IsHomLift (𝟙 A) (ψ.map j.hom) := by
    let : (BasedCategory.ofFunctor
      (Functor.Elements.π (restrictedCoyoneda ξ.base))).p.IsHomLift (𝟙 A) j.hom := hj
    exact BasedFunctor.preserves_isHomLift ψ (𝟙 A) j.hom
  have hi' : p.IsHomLift (𝟙 A) (i.hom.app (G.objects.elementsMk A x)) :=
    hi (G.objects.elementsMk A x)
  have hcomp : p.IsHomLift (𝟙 A) (i.hom.app (G.objects.elementsMk A x) ≫ ψ.map j.hom) := by
    let := hi'
    let := hψj
    simpa only [Category.id_comp] using
      IsHomLift.comp p (𝟙 A) (𝟙 A) (i.hom.app (G.objects.elementsMk A x)) (ψ.map j.hom)
  exact classOf_eq_of_homLift p hp.cofibered (quotientFiberObject G A x)
    ⟨ψ.obj ⟨elementsPointMap φ A x⟩, ψ.w_obj ⟨elementsPointMap φ A x⟩⟩
    (i.hom.app (G.objects.elementsMk A x) ≫ ψ.map j.hom) hcomp

/-- A smooth prorepresentable groupoid in functors is minimal precisely when the kernel of the
differential of `U → [U/R]` is contained in the image of the canonical map `Der_Λ(k, k) → TU`. -/
@[stacks 06KN "part (2): minimal iff the kernel of the differential lies in the image of Der"]
public theorem isMinimal_iff_quotientDifferential_ker_le_derivationRange
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hpro : IsProrepresentable G) (hsmooth : IsSmooth G) :
    IsMinimal.{u, v, w, v} G ↔
      ∀ x : tangentSpaceArtinian.{u, w, v} Λ k
          (isomorphismClasses (BasedCategory.ofFunctor (Functor.Elements.π G.objects))
            (categoryOfElements_projection_isCofibered G.objects)),
        quotientDifferential.{u, v, w} G x =
            quotientDifferential.{u, v, w} G
              (derivationToTangentSpace (Functor.Elements.π G.objects)
                (objects_isPredeformationCategory_of_isProrepresentable G hpro) 0) →
          x ∈ Set.range (derivationToTangentSpace (Functor.Elements.π G.objects)
            (objects_isPredeformationCategory_of_isProrepresentable G hpro)) := by
  classical
  let p := Grothendieck.forget (evaluationFunctor G)
  let 𝓤 := BasedCategory.ofFunctor (Functor.Elements.π G.objects)
  let h𝓤 := categoryOfElements_projection_isCofibered G.objects
  let hUpre := objects_isPredeformationCategory_of_isProrepresentable G hpro
  let hp := quotient_isPredeformationCategory_of_isProrepresentable G hpro
  let hS2 := quotient_schlessingerConditionS2_of_isProrepresentable G hpro hsmooth
  let T := artinianDualNumbers.{u, w, v} Λ k
  let A₀ := residueFieldObject.{u, v, w} Λ k
  let f₀ := derivationMorphism.{u, v, w} (Λ := Λ) (k := k) 0
  have hf₀ : IsDerivationMorphism (0 : Derivation Λ k k) f₀ :=
    derivationMorphism_isDerivationMorphism 0
  constructor
  · rintro ⟨ξ, P, e, hmin, he, ⟨i, hi⟩⟩ x hx
    let φ : BasedFunctor 𝓤
        (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda ξ.base))) :=
      ⟨e.functor, he⟩
    let : φ.toFunctor.Full := inferInstanceAs e.functor.Full
    let : φ.toFunctor.EssSurj := inferInstanceAs e.functor.EssSurj
    obtain ⟨hunique⟩ := restrictedCoyoneda_isPredeformationFunctor ξ.base
    let := hunique
    let a₀ : (restrictedCoyoneda ξ.base).obj A₀ := default
    obtain ⟨x₀, hx₀⟩ := elementsPointMap_surjective φ A₀ a₀
    obtain ⟨xT, rfl⟩ := classOf_surjective 𝓤 h𝓤 T x
    obtain ⟨xT, rfl⟩ := objectFiber_surjective T xT
    let a := elementsPointMap φ T xT
    let b := elementsPointMap φ T (G.objects.map f₀ x₀)
    have hb : b = (restrictedCoyoneda ξ.base).map f₀ a₀ := by
      rw [← hx₀]
      exact elementsPointMap_naturality φ f₀ x₀
    have hbzero (r : ξ.base) : pointDerivation ξ.base b r = 0 := by
      rw [pointDerivation_apply, hb]
      exact (hf₀ (a₀.hom r).down).2
    obtain ⟨δ, hδ⟩ := exists_derivation_of_associatedPointClass_eq hp hS2 ξ hmin P a b (by
      rw [← quotientClass_eq_associatedPointClass G hp ξ P φ i hi T xT,
        ← quotientClass_eq_associatedPointClass G hp ξ P φ i hi T
          (G.objects.map f₀ x₀), ← quotientDifferential_classOf G xT,
        ← quotientDifferential_classOf G (G.objects.map f₀ x₀)]
      exact hx.trans (congrArg (quotientDifferential.{u, v, w} G)
        (derivationToTangentSpace_elements G.objects hUpre 0 x₀ f₀ hf₀)))
    refine ⟨δ, ?_⟩
    have ha : a = (restrictedCoyoneda ξ.base).map
        (derivationMorphism.{u, v, w} δ) a₀ := by
      refine tangentVector_ext fun r => ?_
      have hr := hδ r
      rw [hbzero, zero_add, pointDerivation_apply] at hr
      have ha₀ := a₀.residue_comm r
      change (a₀.hom r).down = residueHom ξ.base r at ha₀
      change (a.hom r).snd.down = δ (a₀.hom r).down
      exact hr.trans (congrArg δ ha₀).symm
    have hxT : xT = G.objects.map (derivationMorphism.{u, v, w} δ) x₀ := by
      apply elementsPointMap_injective φ T
      rwa [elementsPointMap_naturality, hx₀]
    rw [hxT]
    exact derivationToTangentSpace_elements G.objects hUpre δ x₀
      (derivationMorphism δ)
      (derivationMorphism_isDerivationMorphism δ)
  · intro hkernel
    obtain ⟨R, ⟨hUiso⟩⟩ := ((isProrepresentable_iff_objects_arrows G).1 hpro).1
    let eU := elementsEquivOfNatIso hUiso
    have heU : eU.functor ⋙ Functor.Elements.π (restrictedCoyoneda R) =
        Functor.Elements.π G.objects := rfl
    have hunit : ∀ X : G.objects.Elements,
        (Functor.Elements.π G.objects).IsHomLift (𝟙 X.1) (eU.unitIso.hom.app X) := by
      intro X
      refine IsHomLift.of_fac' (Functor.Elements.π G.objects) (𝟙 X.1)
        (eU.unitIso.hom.app X) rfl rfl ?_
      simp [eU, elementsEquivOfNatIso, Functor.Elements.π,
        Functor.Elements.isoMk]
      rfl
    let αto : (restrictedCoyoneda R).Elements ⥤ Grothendieck (evaluationFunctor G) :=
      eU.inverse ⋙ quotientMorphism G
    have hαto : αto ⋙ p = Functor.Elements.π (restrictedCoyoneda R) := by
      change (eU.inverse ⋙ quotientMorphism G) ⋙
        Grothendieck.forget (evaluationFunctor G) =
          Functor.Elements.π (restrictedCoyoneda R)
      rw [Functor.assoc, quotientMorphism_over]
      rfl
    let α : BasedFunctor
        (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda R)))
        (BasedCategory.ofFunctor p) := ⟨αto, hαto⟩
    let P := chosenPushforwardsOfCofibered p hp.cofibered
    obtain ⟨η, e, he, ⟨i, hi⟩⟩ := exists_associatedMorphism_presentation p hp.cofibered
      G.objects R α eU heU P
    let φ : BasedFunctor 𝓤
        (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda η.base))) :=
      ⟨e.functor, he⟩
    let : φ.toFunctor.Full := inferInstanceAs e.functor.Full
    let : φ.toFunctor.EssSurj := inferInstanceAs e.functor.EssSurj
    let ψ := (associatedMorphism hp.cofibered η P).toBasedFunctor
    let j₀ : quotientMorphism G ≅ eU.functor ⋙ αto :=
      (Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight eU.unitIso (quotientMorphism G) ≪≫
          Functor.associator _ _ _
    have hj₀ : ∀ X : G.objects.Elements, p.IsHomLift (𝟙 X.1) (j₀.hom.app X) := by
      intro X
      let : (BasedCategory.ofFunctor
        (Functor.Elements.π G.objects)).p.IsHomLift (𝟙 X.1)
          (eU.unitIso.hom.app X) := hunit X
      have hmap : p.IsHomLift (𝟙 X.1)
          ((quotientMorphism G).map (eU.unitIso.hom.app X)) :=
        BasedFunctor.preserves_isHomLift (quotientBasedFunctor G) (𝟙 X.1)
          (eU.unitIso.hom.app X)
      simpa [j₀, Functor.isoWhiskerRight, quotientBasedFunctor, p,
        BasedCategory.ofFunctor] using hmap
    let j := j₀ ≪≫ i
    have hj : ∀ X : G.objects.Elements, p.IsHomLift (𝟙 X.1) (j.hom.app X) := by
      intro X
      let := hj₀ X
      let := hi X
      have h : p.IsHomLift (𝟙 X.1) (j₀.hom.app X ≫ i.hom.app X) := by
        simpa using IsHomLift.comp p (𝟙 X.1) (𝟙 X.1) (j₀.hom.app X) (i.hom.app X)
      exact h
    let jbased : quotientBasedFunctor G ≅ φ.comp ψ := BasedNatIso.mkNatIso j hj
    have hcomp : Deformation.IsSmooth (φ.comp ψ) :=
      isSmooth_of_basedIso jbased ((source_isSmooth_iff_quotient G).mp hsmooth.1)
    have hψ : Deformation.IsSmooth ψ :=
      isSmooth_of_essSurj_comp φ ψ hcomp
    have hη : IsVersal hp.cofibered η :=
      (isSmooth_associatedMorphism_iff_isVersal hp.cofibered η P).mp hψ
    refine ⟨η, P, e, ?_, he, ⟨⟨j, hj⟩⟩⟩
    apply isMinimalVersal_of_tangentKernel hp.cofibered η hη P
    intro a b hbzero hab
    obtain ⟨hunique⟩ := restrictedCoyoneda_isPredeformationFunctor η.base
    let := hunique
    let a₀ : (restrictedCoyoneda η.base).obj A₀ := default
    obtain ⟨x₀, hx₀⟩ := elementsPointMap_surjective φ A₀ a₀
    obtain ⟨xT, hxT⟩ := elementsPointMap_surjective φ T a
    have hb' : b = elementsPointMap φ T (G.objects.map f₀ x₀) := by
      rw [elementsPointMap_naturality, hx₀]
      exact tangentVector_ext hbzero
    have hdiff : quotientDifferential.{u, v, w} G (classOf 𝓤 h𝓤 (objectFiber T xT)) =
        quotientDifferential.{u, v, w} G
          (derivationToTangentSpace (Functor.Elements.π G.objects) hUpre 0) := by
      rwa [quotientDifferential_classOf G xT,
        derivationToTangentSpace_elements G.objects hUpre 0 x₀ f₀ hf₀,
        quotientDifferential_classOf G (G.objects.map f₀ x₀),
        quotientClass_eq_associatedPointClass G hp η P φ j hj T xT,
        quotientClass_eq_associatedPointClass G hp η P φ j hj T (G.objects.map f₀ x₀),
        hxT, ← hb']
    obtain ⟨δ, hδ⟩ := hkernel _ hdiff
    refine ⟨δ, fun r => ?_⟩
    have hxδ : xT = G.objects.map (derivationMorphism.{u, v, w} δ) x₀ := by
      apply classOf_objectFiber_injective G.objects T
      exact hδ.symm.trans (derivationToTangentSpace_elements G.objects hUpre δ x₀
        (derivationMorphism δ)
        (derivationMorphism_isDerivationMorphism δ))
    have ha : a = (restrictedCoyoneda η.base).map
        (derivationMorphism.{u, v, w} δ) a₀ := by
      rw [← hxT, hxδ, elementsPointMap_naturality, hx₀]
    rw [ha]
    change ((derivationMorphism.{u, v, w} δ).hom (a₀.hom r)).snd.down =
      δ (residueHom η.base r)
    exact ((derivationMorphism_isDerivationMorphism δ)
      (a₀.hom r).down).2.trans (congrArg δ (a₀.residue_comm r))

/-- A minimal smooth prorepresentable groupoid in functors over which the residue field carries no
nonzero `Λ`-derivation is normalized. The hypothesis `hzero` holds when `k` is separable over the
image field of `Λ`. -/
public theorem isNormalized_of_isMinimal_of_derivation_eq_zero
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hpro : IsProrepresentable G) (hsmooth : IsSmooth G) (hmin : IsMinimal.{u, v, w, v} G)
    (hzero : ∀ δ : Derivation Λ k k, δ = 0) :
    IsNormalized.{u, v, w} G := by
  classical
  let p := Grothendieck.forget (evaluationFunctor G)
  let 𝓤 := BasedCategory.ofFunctor (Functor.Elements.π G.objects)
  let h𝓤 := categoryOfElements_projection_isCofibered G.objects
  let 𝓠 := BasedCategory.ofFunctor p
  let h𝓠 := quotientProjection_cofibered G
  let hp := quotient_isPredeformationCategory_of_isProrepresentable G hpro
  let hS2 := quotient_schlessingerConditionS2_of_isProrepresentable G hpro hsmooth
  let T := artinianDualNumbers.{u, w, v} Λ k
  refine (isNormalized_iff_bijective_quotientDifferential.{u, v, w} G).2 ⟨?_, ?_⟩
  · obtain ⟨ξ, P, e, hminimal, he, ⟨i, hi⟩⟩ := hmin
    let φ : BasedFunctor 𝓤
        (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda ξ.base))) :=
      ⟨e.functor, he⟩
    let : φ.toFunctor.Full := inferInstanceAs e.functor.Full
    let ψ := (associatedMorphism hp.cofibered ξ P).toBasedFunctor
    intro x y hxy
    obtain ⟨x, rfl⟩ := classOf_surjective 𝓤 h𝓤 T x
    obtain ⟨x, rfl⟩ := objectFiber_surjective T x
    obtain ⟨y, rfl⟩ := classOf_surjective 𝓤 h𝓤 T y
    obtain ⟨y, rfl⟩ := objectFiber_surjective T y
    let a := elementsPointMap φ T x
    let b := elementsPointMap φ T y
    obtain ⟨δ, hδ⟩ := exists_derivation_of_associatedPointClass_eq hp hS2 ξ hminimal P a b (by
      rwa [← quotientClass_eq_associatedPointClass G hp ξ P φ i hi T x,
        ← quotientClass_eq_associatedPointClass G hp ξ P φ i hi T y,
        ← quotientDifferential_classOf G x, ← quotientDifferential_classOf G y])
    have hab : a = b := by
      refine tangentVector_ext fun r => ?_
      have hr := hδ r
      rw [hzero δ] at hr
      change (a.hom r).snd.down = (b.hom r).snd.down
      rw [← pointDerivation_apply ξ.base a r, ← pointDerivation_apply ξ.base b r]
      simpa using hr
    exact congrArg (fun z : G.objects.obj T => classOf 𝓤 h𝓤 (objectFiber T z))
      (elementsPointMap_injective φ T hab)
  · exact quotientDifferential_surjective G

end GroupoidInFunctors

end

end Deformation
