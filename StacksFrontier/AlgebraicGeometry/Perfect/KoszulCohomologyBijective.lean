module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCechCohomologyOnUnion
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulHomDerivedMorphisms
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulSectionsNaturality

/-!
# The Koszul comparison to cohomology over a union of basic opens is an isomorphism

Let `A` be a commutative ring, let `f = (f₁, …, f_r)` be a finite sequence of elements of `A`,
let `X = Spec A` and let `U = D(f₁) ∪ ⋯ ∪ D(f_r) ⊆ X`.  For an object `E` of `D(𝒪_X)` whose
cohomology sheaves are all quasi-coherent the canonical comparison map

`colimₑ Hom_{D(𝒪_X)}(Iₑ, E) ⟶ H⁰(U, E)`

out of the filtered colimit of the morphism groups from the derived Koszul system is an
isomorphism.  Source and target lie in different universes, so the isomorphism is stated as
bijectivity of the underlying map of groups.

## Main results

* `Koszul.DerivedSystem.bijective_cohomologyComparison`: the comparison map is bijective.
* `Koszul.DerivedSystem.cohomologyEquiv`: the colimit of the morphism groups out of the Koszul
  system is degree-zero hypercohomology over `U`, and
  `Koszul.DerivedSystem.cohomologyEquiv_naturality` says this is natural in the object.
* `Koszul.DerivedSystem.bijective_of_restrictionEquiv`: the formal step. If the morphism groups
  out of the Koszul system admit *some* family of bijections onto `Hom(𝒪_U, E|_U)`, compatible
  with the colimit injections and with composition, then the canonical comparison map is itself
  bijective.
* `Koszul.DerivedSystem.unit_end_comm`, `Koszul.DerivedSystem.derived_unit_end_comm` and
  `Koszul.DerivedSystem.restricted_unit_end_comm`: the endomorphism ring of the structure sheaf,
  in modules, in the derived category, and after restriction to an open subspace, is commutative.

## Implementation notes

The formal step is isolated because the canonical comparison map and the bijection produced by
the Čech–Koszul computation are *a priori* different maps: the computation identifies the colimit
with the cohomology group, but not visibly through the canonical map.  Any two such compatible
families differ by composition with a single endomorphism of `𝒪_U` in `D(𝒪_U)`, and the
endomorphism ring of `𝒪_U` is commutative, so that endomorphism is invertible as soon as one of
the two families is bijective.

The family of bijections is assembled from four identifications: derived sheafification
`D(A) ⥤ D(𝒪_X)` is fully faithful with essential image the complexes with quasi-coherent
cohomology, which turns the question into one about a complex of `A`-modules; the degree-zero
homology of the Hom complex out of a bounded above complex of projectives computes morphisms in
`D(A)`, and every Koszul stage is such a complex; the filtered colimit of those Hom complexes is
the total alternating Čech complex of the associated complex of sheaves; and that total complex
computes hypercohomology over `U`, the finite intersections of the covering basic opens being
affine.  A representing complex of `A`-modules is chosen for each object, and the resulting family
is natural because derived sheafification is full, so every morphism between representable
objects is itself represented.

## References

* [Stacks Project, Tag 08DD](https://stacks.math.columbia.edu/tag/08DD)
* [Stacks Project, Tag 08DC](https://stacks.math.columbia.edu/tag/08DC)
* [Stacks Project, Tag 08CZ](https://stacks.math.columbia.edu/tag/08CZ)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0A66](https://stacks.math.columbia.edu/tag/0A66)
* [Stacks Project, Tag 08D1](https://stacks.math.columbia.edu/tag/08D1)
* [Stacks Project, Tag 08D2](https://stacks.math.columbia.edu/tag/08D2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace Koszul.DerivedSystem

/-! ### The formal step -/

/-- **Any family of bijections compatible with composition makes the canonical comparison
bijective.**

Let `R : C ⥤ D` be a functor, let `I : ℕᵒᵖ ⥤ C` be a system with a morphism `a : I ⟶ O` to a
constant object `O`, and suppose each `a` becomes invertible under `R`, with inverse isomorphism
`e n : R O ≅ R (I n)`. Let `P` be a property of objects satisfied by `O` and by every `I n`.

The canonical map `c X : colimₑ Hom(Iₑ, X) → (R O ⟶ R X)` sends the class of `α : I n ⟶ X` to
`(e n).hom ≫ R α`. If some family `s X` of bijections with the same source and target satisfies
the composition rule `sn`, and if the endomorphisms of `R O` commute with one another, then
`c X` is bijective for every `X` satisfying `P`.

Indeed `sn` forces `s X x = h ≫ c X x` for the single morphism `h = s O (class of a)`, and
surjectivity of `s O` then exhibits an inverse of `h` in the commutative endomorphism ring of
`R O`. -/
theorem bijective_of_restrictionEquiv
    {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type*} [Category* D] (R : C ⥤ D)
    (I : ℕᵒᵖ ⥤ C) (O : C)
    (a : I ⟶ (Functor.const ℕᵒᵖ).obj O)
    (e : ∀ n, R.obj O ≅ R.obj (I.obj (op n)))
    (he : ∀ n, (e n).inv = R.map (a.app (op n)))
    (P : C → Prop) (hI : ∀ n, P (I.obj (op n))) (hO : P O)
    (s : ∀ X, P X → ↥(colimit (I.rightOp ⋙ preadditiveYoneda.obj X)) ≃
      (R.obj O ⟶ R.obj X))
    (sn : ∀ X (hX : P X) n (g : I.obj (op n) ⟶ X),
      s X hX (colimit.ι (I.rightOp ⋙ preadditiveYoneda.obj X) n g) =
      s (I.obj (op n)) (hI n)
        (colimit.ι (I.rightOp ⋙ preadditiveYoneda.obj (I.obj (op n))) n (𝟙 _)) ≫ R.map g)
    (c : ∀ X, ↥(colimit (I.rightOp ⋙ preadditiveYoneda.obj X)) → (R.obj O ⟶ R.obj X))
    (cn : ∀ X n (g : I.obj (op n) ⟶ X),
      c X (colimit.ι (I.rightOp ⋙ preadditiveYoneda.obj X) n g) =
        (e n).hom ≫ R.map g)
    (comm : ∀ h k : R.obj O ⟶ R.obj O, h ≫ k = k ≫ h)
    (X : C) (hX : P X) : Function.Bijective (c X) := by
  let h := s O hO (colimit.ι (I.rightOp ⋙ preadditiveYoneda.obj O) 0 (a.app (op 0)))
  have common (n : ℕ) :
      s O hO (colimit.ι (I.rightOp ⋙ preadditiveYoneda.obj O) n (a.app (op n))) = h := by
    congr 1
    have hw := ConcreteCategory.congr_hom
      (colimit.w (I.rightOp ⋙ preadditiveYoneda.obj O) (homOfLE (Nat.zero_le n)))
      (a.app (op 0))
    change colimit.ι (I.rightOp ⋙ preadditiveYoneda.obj O) n
      (I.map (homOfLE (Nat.zero_le n)).op ≫ a.app (op 0)) = _ at hw
    rw [show I.map (homOfLE (Nat.zero_le n)).op ≫ a.app (op 0) =
      a.app (op n) by simp [a.naturality (homOfLE (Nat.zero_le n)).op]] at hw
    exact hw
  have hs (Y : C) (hY : P Y) (x : ↥(colimit (I.rightOp ⋙ preadditiveYoneda.obj Y))) :
      s Y hY x = h ≫ c Y x := by
    let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{v}) :=
      preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{v})
    obtain ⟨n, g, rfl⟩ := Concrete.colimit_exists_rep _ x
    change I.obj (op n) ⟶ Y at g
    rw [sn Y hY n g, cn Y n g]
    have hn := (sn O hO n (a.app (op n))).symm.trans (common n)
    rw [← he n] at hn
    rw [(Iso.comp_inv_eq _).mp hn, Category.assoc]
  obtain ⟨x, hx⟩ := (s O hO).surjective (𝟙 _)
  have hk : h ≫ c O x = 𝟙 _ := (hs O hO x).symm.trans hx
  have kh : c O x ≫ h = 𝟙 _ := (comm _ _).symm.trans hk
  refine ⟨fun b b' hb ↦ (s X hX).injective (by rw [hs, hs, hb]), fun y ↦ ?_⟩
  obtain ⟨b, hb⟩ := (s X hX).surjective (h ≫ y)
  exact ⟨b, by
    simpa only [← Category.assoc, kh, Category.id_comp] using
      congrArg (c O x ≫ ·) ((hs X hX b).symm.trans hb)⟩

/-! ### The endomorphisms of the restricted structure sheaf commute -/

section EndComm

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (U : Opens X)

open ExtensionByZeroModules Stacks.Cohomology.OpenSubspace

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The derived restriction of the structure sheaf is the structure sheaf of the open
subspace.** Restriction is exact, so it commutes with placing a module in degree zero. -/
public def restrictedStructureSheafIso :
    (derivedRestriction O U).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).obj
          (SheafOfModules.unit O)) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (resRing U O)) 0).obj
        (SheafOfModules.unit (resRing U O)) :=
  (derivedRestrictionIso O U).app _ ≪≫
    ((jStar U O).mapDerivedCategorySingleFunctor 0).app (SheafOfModules.unit O)

end EndComm

section UnitEnd

open scoped IsMulCommutative

variable {Y : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u})
  [∀ V, IsMulCommutative (R.obj.obj V)]

/-- **The endomorphism ring of the structure sheaf is commutative.** An endomorphism of the
sheaf of rings viewed as a module over itself is multiplication by its value on `1`, and the
sections of the sheaf commute. -/
public lemma unit_end_comm (a b : SheafOfModules.unit R ⟶ SheafOfModules.unit R) :
    a ≫ b = b ≫ a := by
  ext V
  let av : (R.obj.obj V) →ₗ[R.obj.obj V] (R.obj.obj V) := (a.val.app V).hom
  let bv : (R.obj.obj V) →ₗ[R.obj.obj V] (R.obj.obj V) := (b.val.app V).hom
  change bv (av 1) = av (bv 1)
  have hmul (φ : R.obj.obj V →ₗ[R.obj.obj V] R.obj.obj V) (y : R.obj.obj V) :
      φ y = y * φ 1 := by
    simpa using φ.map_smul y 1
  rw [hmul bv (av 1), hmul av (bv 1), mul_comm]

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The endomorphism ring of the structure sheaf in the derived category is commutative.**
Placing a module in degree zero is fully faithful, so these endomorphisms are the
endomorphisms of the structure sheaf itself. -/
public lemma derived_unit_end_comm
    (a b : (DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0).obj
        (SheafOfModules.unit R) ⟶
      (DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0).obj (SheafOfModules.unit R)) :
    a ≫ b = b ≫ a := by
  let F := DerivedCategory.singleFunctor (SheafOfModules.{u} R) 0
  obtain ⟨a, rfl⟩ := F.map_surjective a
  obtain ⟨b, rfl⟩ := F.map_surjective b
  rw [← F.map_comp, ← F.map_comp, unit_end_comm R]

end UnitEnd

section RestrictedUnitEnd

open scoped IsMulCommutative
open ExtensionByZeroModules Stacks.Cohomology.OpenSubspace

attribute [local instance 10000] HasDerivedCategory.standard

variable {Y : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) (V : Opens Y)
  [∀ W, IsMulCommutative ((resRing V O).obj.obj W)]

/-- **The endomorphism ring of the restricted structure sheaf in the derived category is
commutative.** -/
public lemma restricted_unit_end_comm
    (a b : (derivedRestriction O V).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).obj
          (SheafOfModules.unit O)) ⟶
      (derivedRestriction O V).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).obj
          (SheafOfModules.unit O))) : a ≫ b = b ≫ a := by
  apply ((restrictedStructureSheafIso O V).homCongr
    (restrictedStructureSheafIso O V)).injective
  rw [Iso.homCongr_comp, Iso.homCongr_comp]
  exact derived_unit_end_comm (resRing V O) _ _

end RestrictedUnitEnd

/-! ### The morphism colimit is hypercohomology over the union -/

section Assembly

open Stacks.Koszul.Cech

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : CommRingCat.{u}} {r : ℕ}

/-- Having quasi-coherent cohomology sheaves in every degree. -/
abbrev HasQuasicoherentCohomology (A : CommRingCat.{u}) (E : derivedCat A) : Prop :=
  ∀ i : ℤ, ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (Spec A).ringCatSheaf) i).obj E).IsQuasicoherent

/-- Derived sheafification is fully faithful. -/
public def derivedSheafifyFullyFaithful (A : CommRingCat.{u}) :
    (derivedSheafify A).FullyFaithful :=
  AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful A

public instance derivedSheafify_full (A : CommRingCat.{u}) : (derivedSheafify A).Full :=
  (derivedSheafifyFullyFaithful A).full

public instance derivedSheafify_faithful (A : CommRingCat.{u}) : (derivedSheafify A).Faithful :=
  (derivedSheafifyFullyFaithful A).faithful

/-- A complex of associated sheaves has quasi-coherent cohomology. -/
public theorem hasQuasicoherentCohomology_derivedSheafify (A : CommRingCat.{u})
    (N : DerivedCategory (ModuleCat.{u} A)) :
    HasQuasicoherentCohomology A ((derivedSheafify A).obj N) :=
  fun i ↦ AlgebraicGeometry.isQuasicoherent_homology_mapDerivedCategory_obj A N i

/-- **An object with quasi-coherent cohomology is a complex of associated sheaves.** -/
public theorem exists_iso_derivedSheafify (A : CommRingCat.{u}) (E : derivedCat A)
    (hE : HasQuasicoherentCohomology A E) :
    ∃ N : DerivedCategory (ModuleCat.{u} A),
      Nonempty ((derivedSheafify A).obj N ≅ E) :=
  AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory A E hE

/-- A chosen complex of `A`-modules representing an object with quasi-coherent cohomology. -/
def qcModel {A : CommRingCat.{u}} (E : derivedCat A) (hE : HasQuasicoherentCohomology A E) :
    DerivedCategory (ModuleCat.{u} A) :=
  (exists_iso_derivedSheafify A E hE).choose

/-- The chosen isomorphism exhibiting an object with quasi-coherent cohomology as a complex of
associated sheaves. -/
def qcModelIso {A : CommRingCat.{u}} (E : derivedCat A) (hE : HasQuasicoherentCohomology A E) :
    (derivedSheafify A).obj (qcModel E hE) ≅ E :=
  Classical.choice (exists_iso_derivedSheafify A E hE).choose_spec

/-- The diagram of morphism groups out of the derived Koszul system, as a functor of the
target. -/
abbrev homGroupFunctor (f : Fin r → A) : derivedCat A ⥤ (ℕ ⥤ AddCommGrpCat.{u + 1}) :=
  homDiagramFunctor (koszulDerivedSystem f)

/-- **The colimit of the morphism groups out of the Koszul system, for a complex of associated
sheaves, is degree-zero hypercohomology over the union of the basic opens.** -/
def affineHomCohomologyIso (f : Fin r → A) :
    koszulDerivedHomDiagramFunctor f ⋙ colim ≅
      derivedSheafify A ⋙ sectionsOnUnion f ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    AddCommGrpCat.{u + 1}).preimageIso
    (koszulDerivedHomColimitIsoCech f ≪≫
      Functor.isoWhiskerRight (cechCohomologyIso f) AddCommGrpCat.uliftFunctor.{u + 1, u} ≪≫
      Functor.isoWhiskerRight ((sheafifyModule A).mapDerivedCategoryFactors).symm
        (sectionsOnUnion f ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}))

/-- The same identification, read on the morphism groups out of the derived Koszul system. -/
def sheafifiedHomCohomologyIso (f : Fin r → A) :
    derivedSheafify A ⋙ homGroupFunctor f ⋙ colim ≅
      derivedSheafify A ⋙ sectionsOnUnion f ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  (Functor.isoWhiskerRight
      (homDiagramMapIso (derivedSheafify A)
        (koszulCochainDiagram f ⋙ DerivedCategory.Q)) colim).symm ≪≫
    affineHomCohomologyIso f

/-- Transporting a natural isomorphism along chosen isomorphisms is natural. -/
private theorem transport_natural {C : Type*} [Category* C] {D : Type*} [Category* D]
    (S : C ⥤ D) [S.Full] {Φ Ψ : D ⥤ AddCommGrpCat.{v}} (θ : S ⋙ Φ ≅ S ⋙ Ψ)
    {N N' : C} {E E' : D} (eN : S.obj N ≅ E) (eN' : S.obj N' ≅ E') (g : E ⟶ E') :
    Φ.map g ≫ Φ.map eN'.inv ≫ θ.hom.app N' ≫ Ψ.map eN'.hom =
      (Φ.map eN.inv ≫ θ.hom.app N ≫ Ψ.map eN.hom) ≫ Ψ.map g := by
  obtain ⟨h, hh⟩ := S.map_surjective (eN.hom ≫ g ≫ eN'.inv)
  have hθ : Φ.map (S.map h) ≫ θ.hom.app N' = θ.hom.app N ≫ Ψ.map (S.map h) :=
    θ.hom.naturality h
  rw [hh] at hθ
  simp only [Functor.map_comp, Category.assoc] at hθ
  calc Φ.map g ≫ Φ.map eN'.inv ≫ θ.hom.app N' ≫ Ψ.map eN'.hom
      = (Φ.map eN.inv ≫ Φ.map eN.hom) ≫
          Φ.map g ≫ Φ.map eN'.inv ≫ θ.hom.app N' ≫ Ψ.map eN'.hom := by
        rw [eN.inv_hom_id_map Φ, Category.id_comp]
    _ = Φ.map eN.inv ≫
          (Φ.map eN.hom ≫ Φ.map g ≫ Φ.map eN'.inv ≫ θ.hom.app N') ≫ Ψ.map eN'.hom := by
        simp only [Category.assoc]
    _ = Φ.map eN.inv ≫
          (θ.hom.app N ≫ Ψ.map eN.hom ≫ Ψ.map g ≫ Ψ.map eN'.inv) ≫ Ψ.map eN'.hom := by
        rw [hθ]
    _ = (Φ.map eN.inv ≫ θ.hom.app N ≫ Ψ.map eN.hom) ≫ Ψ.map g := by
        simp only [Category.assoc, eN'.inv_hom_id_map Ψ, Category.comp_id]

/-- **The colimit of the morphism groups out of the Koszul system is degree-zero
hypercohomology over `U`**, for every object with quasi-coherent cohomology. -/
def cohomologyEquiv (f : Fin r → A) (E : derivedCat A)
    (hE : HasQuasicoherentCohomology A E) :
    ↥(colimit (homGroupSystem f E)) ≃+ ↥((sectionsOnUnion f).obj E) :=
  ((((homGroupFunctor f ⋙ colim).mapIso (qcModelIso E hE).symm) ≪≫
      (sheafifiedHomCohomologyIso f).app (qcModel E hE) ≪≫
      (sectionsOnUnion f ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}).mapIso
        (qcModelIso E hE)).addCommGroupIsoToAddEquiv).trans
    AddEquiv.ulift

/-- The identification is natural in the object. -/
theorem cohomologyEquiv_naturality (f : Fin r → A) (E E' : derivedCat A)
    (hE : HasQuasicoherentCohomology A E) (hE' : HasQuasicoherentCohomology A E')
    (g : E ⟶ E') (x : ↥(colimit (homGroupSystem f E))) :
    cohomologyEquiv f E' hE' (((homGroupFunctor f ⋙ colim).map g) x) =
      ((sectionsOnUnion f).map g).hom (cohomologyEquiv f E hE x) :=
  congrArg ULift.down (ConcreteCategory.congr_hom
    (transport_natural (derivedSheafify A) (sheafifiedHomCohomologyIso f)
      (qcModelIso E hE) (qcModelIso E' hE') g) x)

/-- The Koszul stages have quasi-coherent cohomology, being complexes of associated sheaves. -/
public theorem hasQuasicoherentCohomology_koszulDerivedSystem (f : Fin r → A) (n : ℕ) :
    HasQuasicoherentCohomology A ((koszulDerivedSystem f).obj (op n)) :=
  hasQuasicoherentCohomology_derivedSheafify A _

/-- The structure sheaf has quasi-coherent cohomology. -/
public theorem hasQuasicoherentCohomology_structureSheafObject (A : CommRingCat.{u}) :
    HasQuasicoherentCohomology A (structureSheafObject A) := fun i ↦
  (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (Spec A).ringCatSheaf) i).mapIso
      (derivedRingObjectIso A))
    (hasQuasicoherentCohomology_derivedSheafify A _ i)

/-- The sections of the structure sheaf over the opens of `U` commute. -/
public instance isMulCommutative_resRing_unionOfBasicOpens (f : Fin r → A)
    (W : (Opens (ExtensionByZeroModules.Usp (unionOfBasicOpens f)))ᵒᵖ) :
    IsMulCommutative ((ExtensionByZeroModules.resRing (unionOfBasicOpens f)
      (Spec A).ringCatSheaf).obj.obj W) :=
  inferInstanceAs (IsMulCommutative ((unionOfBasicOpens f).toScheme.sheaf.obj.obj W))

/-- The restriction to `U` of the canonical map `Iₑ ⟶ 𝒪_X` is the inverse of the chosen
isomorphism `𝒪_U ≅ Iₑ|_U`. -/
public theorem restrictionIsoOfUnion_inv' (f : Fin r → A) (n : ℕ) :
    (restrictionIsoOfUnion f n).inv =
      (restrictionToUnion f).map ((koszulSystemToStructureSheaf f).app (op n)) := by
  rw [restrictionIsoOfUnion_inv, koszulSystemToStructureSheaf_app]

/-- The transported identification is compatible with composition: its value on a morphism
out of a Koszul stage is its value on the identity followed by that morphism. -/
public theorem cohomologyEquivHom_comp (f : Fin r → A) (X : derivedCat A)
    (hX : HasQuasicoherentCohomology A X) (n : ℕ)
    (g : (koszulDerivedSystem f).obj (op n) ⟶ X) :
    (sectionsEquivOfUnion f X).symm
        (cohomologyEquiv f X hX (colimit.ι (homGroupSystem f X) n g)) =
      (sectionsEquivOfUnion f ((koszulDerivedSystem f).obj (op n))).symm
          (cohomologyEquiv f ((koszulDerivedSystem f).obj (op n))
            (hasQuasicoherentCohomology_koszulDerivedSystem f n)
            (colimit.ι (homGroupSystem f ((koszulDerivedSystem f).obj (op n))) n (𝟙 _))) ≫
        (restrictionToUnion f).map g := by
  apply (sectionsEquivOfUnion f X).injective
  rw [AddEquiv.apply_symm_apply, sectionsEquivOfUnion_naturality, AddEquiv.apply_symm_apply,
    ← cohomologyEquiv_naturality f _ X (hasQuasicoherentCohomology_koszulDerivedSystem f n) hX g]
  congr 1
  symm
  change (colimit.ι (homGroupSystem f ((koszulDerivedSystem f).obj (op n))) n ≫
    colim.map (Functor.whiskerLeft (koszulDerivedSystem f).rightOp
      (preadditiveYoneda.map g))) (𝟙 _) = _
  rw [colimit.ι_map]
  change colimit.ι (homGroupSystem f X) n (𝟙 _ ≫ g) = _
  rw [Category.id_comp]

/-- **The comparison map of [Stacks, Tag 08DC] is bijective.** For every object `E` of `D(𝒪_X)`
with quasi-coherent cohomology sheaves the canonical comparison map

`colimₑ Hom_{D(𝒪_X)}(Iₑ, E) ⟶ H⁰(U, E)`

over `U = D(f₁) ∪ ⋯ ∪ D(f_r)` is bijective.

[Stacks, Tag 08DD] is registered on another declaration, so no tag attribute is placed here. -/
public theorem bijective_cohomologyComparison (f : Fin r → A) (E : derivedCat A)
    (hE : HasQuasicoherentCohomology A E) :
    Function.Bijective (cohomologyComparison f E) := by
  have hc := bijective_of_restrictionEquiv (restrictionToUnion f) (koszulDerivedSystem f)
    (structureSheafObject A) (koszulSystemToStructureSheaf f) (restrictionIsoOfUnion f)
    (restrictionIsoOfUnion_inv' f)
    (HasQuasicoherentCohomology A) (hasQuasicoherentCohomology_koszulDerivedSystem f)
    (hasQuasicoherentCohomology_structureSheafObject A)
    (fun X hX ↦ ((cohomologyEquiv f X hX).trans (sectionsEquivOfUnion f X).symm).toEquiv)
    (cohomologyEquivHom_comp f)
    (fun X x ↦ cohomologyComparisonHom f X x)
    (cohomologyComparisonHom_colimit_ι f)
    (restricted_unit_end_comm (Spec A).ringCatSheaf (unionOfBasicOpens f)) E hE
  exact (sectionsEquivOfUnion f E).bijective.comp hc

end Assembly

end Koszul.DerivedSystem

end
