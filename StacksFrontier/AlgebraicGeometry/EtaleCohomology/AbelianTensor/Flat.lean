module
public import StacksFrontier.Algebra.Homology.FiniteFreeComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleTensor
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.RingTheory.Etale.Basic

public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianLowerShriek.Exact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbelianTensor.Additive
public import StacksFrontier.CategoryTheory.Sites.MonoidalColimits

/-!
# Flat abelian étale sheaves

An abelian sheaf `F` on the small étale site of a scheme `X` (with values in
`AddCommGrpCat.{max (u + 1) v}`) is *flat* when tensoring with it, for the monoidal structure
`Stacks.EtaleCohomology.etaleAbelianMonoidalCategory`, preserves monomorphisms. Since tensoring is
right exact, a flat sheaf is one for which tensoring with it is exact, on either side.

Over `ℤ` flatness is torsion-freeness, and this holds for sheaves as well: `F` is flat exactly when
multiplication by every nonzero integer on `F` is a monomorphism. Everything else is read off that
criterion.

## Main definitions

* `Stacks.EtaleCohomology.IsFlat`: flatness of an abelian étale sheaf.

## Main results

* `Stacks.EtaleCohomology.isFlat_iff_mono_zsmul`: flat is torsion-free.
* `Stacks.EtaleCohomology.IsFlat.preservesFiniteLimits_tensorRight`, `..._tensorLeft`,
  `IsFlat.shortExact_map_tensorRight`, `IsFlat.shortExact_map_tensorLeft`,
  `IsFlat.acyclic_map_tensorRight`, `IsFlat.acyclic_map_tensorLeft`: tensoring with a flat sheaf
  is exact, keeps short exact sequences short exact and acyclic complexes acyclic.
* `Stacks.EtaleCohomology.IsFlat.of_mono`: a subsheaf of a flat sheaf is flat.
* `Stacks.EtaleCohomology.isFlat_biprod`, `isFlat_sigma`, `isFlat_colimit`,
  `isFlat_colimit_nat`: finite and arbitrary direct sums, and colimits along shapes with exact
  colimits (sequential colimits in particular), of flat sheaves are flat.
* `Stacks.EtaleCohomology.isFlat_constantSheaf`: the constant sheaf of a torsion-free abelian
  group is flat; more generally `isFlat_presheafToSheaf_obj`.
* `Stacks.EtaleCohomology.exists_epi_isFlat`: every abelian étale sheaf is a quotient of a flat
  one.
* `Stacks.EtaleCohomology.preservesColimitsOfSize_tensorLeft`,
  `preservesColimitsOfSize_tensorRight`: tensoring with a fixed sheaf preserves colimits.
* `AddCommGrpCat.mono_whiskerRight_of_mono_zsmul`, `AddCommGrpCat.mono_whiskerLeft_of_mono_zsmul`:
  tensoring with a torsion-free abelian group preserves monomorphisms.

## Implementation notes

That a torsion-free sheaf is flat is checked on sections, with no stalks: the sections of a
torsion-free sheaf are torsion-free abelian groups, hence flat (Mathlib's
`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`, over the universe-lifted copy of `ℤ` the tensor
product of abelian groups is built from), and `f ⊗ F` is the sheafification of the sectionwise
`f ⊗ F` (`CategoryTheory.Sheaf.tensorRightIso`), sheafification preserving monomorphisms. The
converse tensors the monomorphism `n` of the tensor unit, which is the sheafification of the
constant presheaf `ℤ`, with `F`.

Colimits of abelian étale sheaves are not found by instance search (see
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleColimits`), so the
statements about colimits take the existence of the colimits as an instance argument, and the
scoped instances `AlgebraicGeometry.Scheme.SmallEtaleColimits` are opened only around the
statements about sequential colimits. Universe levels of `IsFlat` are given explicitly where the
argument is a biproduct, whose instance search otherwise runs before they are determined.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w u v

/-- An additive functor preserving monomorphisms preserves the monomorphism `n • 𝟙 A`. -/
private theorem mono_zsmul_id_obj {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (G : C ⥤ D) [G.Additive] [G.PreservesMonomorphisms] {A : C} (n : ℤ)
    (h : Mono (n • 𝟙 A)) : Mono (n • 𝟙 (G.obj A)) := by
  have : Mono (G.map (n • 𝟙 A)) := G.map_mono _
  rwa [Functor.map_zsmul, G.map_id] at this

namespace AddCommGrpCat

attribute [local instance] AddCommGrpCat.monoidalCategory AddCommGrpCat.braidedCategoryGeneral

/-- The universe-lifted integers are a domain. -/
lemma isDomain_uliftInt : IsDomain (ULiftInt.{w}) :=
  MulEquiv.isDomain ℤ ULift.ringEquiv.toMulEquiv

/-- The universe-lifted integers are a principal ideal ring. -/
lemma isPrincipalIdealRing_uliftInt_unconditional : IsPrincipalIdealRing (ULiftInt.{w}) :=
  IsPrincipalIdealRing.of_surjective (ULift.ringEquiv.{0, w} (R := ℤ)).symm
    (ULift.ringEquiv.{0, w} (R := ℤ)).symm.surjective

/-- A module over the universe-lifted integers on which multiplication by every nonzero integer
is a monomorphism is flat. -/
lemma flat_of_mono_zsmul (M : ModuleCat.{w} ULiftInt.{w})
    (hM : ∀ n : ℤ, n ≠ 0 → Mono (n • 𝟙 M)) : Module.Flat ULiftInt.{w} M := by
  have := isDomain_uliftInt.{w}
  have := isPrincipalIdealRing_uliftInt_unconditional.{w}
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro x hx
  obtain ⟨⟨r, hr⟩, hrx⟩ := (Submodule.mem_torsion_iff x).1 hx
  have hr0 : r.down ≠ 0 := fun h ↦ nonZeroDivisors.ne_zero hr (ULift.ext h)
  have hinj := (ModuleCat.mono_iff_injective (r.down • 𝟙 M)).1 (hM _ hr0)
  have hrr : r = ((r.down : ℤ) : ULiftInt.{w}) := by
    cases r
    ext
    simp
  refine (Submodule.mem_bot _).2 (hinj ?_)
  show r.down • x = r.down • (0 : M)
  rw [smul_zero, ← Int.cast_smul_eq_zsmul ULiftInt.{w}, ← hrr]
  exact hrx

/-- **Tensoring with a torsion-free abelian group preserves monomorphisms**: such a group is a
flat module over (a universe-lifted copy of) `ℤ`. -/
theorem mono_whiskerRight_of_mono_zsmul {A : AddCommGrpCat.{w}}
    (hA : ∀ n : ℤ, n ≠ 0 → Mono (n • 𝟙 A)) {G H : AddCommGrpCat.{w}} (f : G ⟶ H) [Mono f] :
    Mono (f ▷ A) := by
  let e := uliftIntEquivalence.{w}
  let : e.inverse.Additive := e.inverse.additive_of_preserves_binary_products
  have : Module.Flat ULiftInt.{w} (e.inverse.obj A) := by
    exact flat_of_mono_zsmul _ fun n hn ↦ mono_zsmul_id_obj e.inverse n (hA n hn)
  have : PreservesFiniteLimits (tensorRight (e.inverse.obj A)) := inferInstance
  show Mono (e.functor.map (e.inverse.map f ▷ e.inverse.obj A))
  have : Mono (e.inverse.map f ▷ e.inverse.obj A) :=
    (tensorRight (e.inverse.obj A)).map_mono (e.inverse.map f)
  exact e.functor.map_mono _

/-- **Tensoring on the left with a torsion-free abelian group preserves monomorphisms.** -/
theorem mono_whiskerLeft_of_mono_zsmul {A : AddCommGrpCat.{w}}
    (hA : ∀ n : ℤ, n ≠ 0 → Mono (n • 𝟙 A)) {G H : AddCommGrpCat.{w}} (f : G ⟶ H) [Mono f] :
    Mono (A ◁ f) := by
  have := mono_whiskerRight_of_mono_zsmul hA f
  have h := NatIso.naturality_2 (BraidedCategory.tensorLeftIsoTensorRight A) f
  show Mono ((tensorLeft A).map f)
  rw [← h]
  dsimp
  infer_instance

/-- Multiplication by a nonzero integer on the tensor unit of abelian groups is a
monomorphism. -/
lemma mono_zsmul_id_tensorUnit (n : ℤ) (hn : n ≠ 0) : Mono (n • 𝟙 (𝟙_ AddCommGrpCat.{w})) := by
  let e := uliftIntEquivalence.{w}
  let : e.functor.Additive := e.functor.additive_of_preserves_binary_products
  have : Mono (n • 𝟙 (ModuleCat.of ULiftInt.{w} ULiftInt.{w})) := by
    rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    change n • x = n • y at hxy
    ext
    exact smul_right_injective ℤ hn (congrArg ULift.down hxy)
  exact mono_zsmul_id_obj e.functor n this

end AddCommGrpCat

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

attribute [local instance] AddCommGrpCat.monoidalCategory AddCommGrpCat.braidedCategoryGeneral
  AddCommGrpCat.monoidalClosedGeneral etaleAbelianMonoidalCategory

variable {X : Scheme.{u}}

/-- In a preadditive category, multiplication by an integer on an object is a monomorphism as
soon as it is one on an isomorphic object. -/
lemma mono_zsmul_id_of_iso {C : Type*} [Category C] [Preadditive C] {A B : C} (e : A ≅ B)
    (n : ℤ) [Mono (n • 𝟙 B)] : Mono (n • 𝟙 A) := by
  have h : n • 𝟙 A = e.hom ≫ (n • 𝟙 B) ≫ e.inv := by
    simp [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  rw [h]
  infer_instance

/-- An abelian sheaf on the small étale site is **flat** when tensoring with it preserves
monomorphisms. Tensoring is right exact, so this is the exactness of `- ⊗ F`
(`Stacks.EtaleCohomology.IsFlat.preservesFiniteLimits_tensorRight`); by the braiding it is also
the exactness of `F ⊗ -`. -/
def IsFlat (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) : Prop :=
  (tensorRight F).PreservesMonomorphisms

/-- The sections of an abelian étale sheaf on which multiplication by `n` is a monomorphism
inherit that property. -/
lemma mono_zsmul_app_of_mono_zsmul {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    {n : ℤ} (h : Mono (n • 𝟙 F)) (U : X.Etaleᵒᵖ) : Mono (n • 𝟙 (F.obj.obj U)) := by
  have : Mono (n • 𝟙 F).hom := inferInstance
  have h' : (n • 𝟙 F).hom.app U = n • 𝟙 (F.obj.obj U) := rfl
  rw [← h']
  infer_instance

/-- The sheafification of a morphism of presheaves of abelian groups which is a monomorphism on
sections is a monomorphism. -/
private theorem mono_presheafToSheaf_map_of_mono_app
    {P Q : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}} (g : P ⟶ Q) (h : ∀ U, Mono (g.app U)) :
    Mono ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).map g) := by
  have : Mono g := NatTrans.mono_of_mono_app _
  infer_instance

/-- **A torsion-free abelian étale sheaf is flat**: its sections are torsion-free abelian groups,
so tensoring with them sectionwise preserves monomorphisms, and so does sheafification. -/
theorem isFlat_of_mono_zsmul {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    (hF : ∀ n : ℤ, n ≠ 0 → Mono (n • 𝟙 F)) : IsFlat F := by
  let := isMonoidal_W_smallEtale.{u, v} X
  constructor
  intro G H f _
  rw [← NatIso.naturality_2 (Sheaf.tensorRightIso X.smallEtaleTopology F) f]
  have : Mono ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).map
      (f.hom ▷ F.obj)) := by
    refine mono_presheafToSheaf_map_of_mono_app _ fun U ↦ ?_
    have : Mono (f.hom.app U) := inferInstance
    exact AddCommGrpCat.mono_whiskerRight_of_mono_zsmul
      (fun n hn ↦ mono_zsmul_app_of_mono_zsmul (hF n hn) U) (f.hom.app U)
  dsimp
  infer_instance

/-- **Tensoring on the left with a torsion-free abelian étale sheaf preserves
monomorphisms.** -/
theorem preservesMonomorphisms_tensorLeft_of_mono_zsmul
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    (hF : ∀ n : ℤ, n ≠ 0 → Mono (n • 𝟙 F)) : (tensorLeft F).PreservesMonomorphisms := by
  let := isMonoidal_W_smallEtale.{u, v} X
  constructor
  intro G H f _
  rw [← NatIso.naturality_2 (Sheaf.tensorLeftIso X.smallEtaleTopology F) f]
  have : Mono ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).map
      (F.obj ◁ f.hom)) := by
    refine mono_presheafToSheaf_map_of_mono_app _ fun U ↦ ?_
    have : Mono (f.hom.app U) := inferInstance
    exact AddCommGrpCat.mono_whiskerLeft_of_mono_zsmul
      (fun n hn ↦ mono_zsmul_app_of_mono_zsmul (hF n hn) U) (f.hom.app U)
  dsimp
  infer_instance

/-- The sheafification of a presheaf of abelian groups whose sections are torsion-free is
torsion-free. -/
lemma mono_zsmul_presheafToSheaf_obj (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) (n : ℤ)
    (hP : ∀ U, Mono (n • 𝟙 (P.obj U))) :
    Mono (n • 𝟙 ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj P)) := by
  refine mono_zsmul_id_obj (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) n ?_
  have (U : X.Etaleᵒᵖ) : Mono ((n • 𝟙 P).app U) := hP U
  exact NatTrans.mono_of_mono_app _

/-- Multiplication by a nonzero integer on the tensor unit of abelian étale sheaves is a
monomorphism: the unit is the sheafification of the constant presheaf with value the tensor
unit of abelian groups. -/
lemma mono_zsmul_id_tensorUnit (n : ℤ) (hn : n ≠ 0) :
    Mono (n • 𝟙 (𝟙_ (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))) := by
  let := isMonoidal_W_smallEtale.{u, v} X
  have := mono_zsmul_presheafToSheaf_obj (𝟙_ (X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})) n
    (fun _ ↦ AddCommGrpCat.mono_zsmul_id_tensorUnit n hn)
  exact mono_zsmul_id_of_iso
    (Functor.Monoidal.εIso (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) n

/-- **A flat abelian étale sheaf is torsion-free**: tensoring the monomorphism `n` of the tensor
unit with it gives multiplication by `n`. -/
theorem mono_zsmul_of_isFlat {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    (hF : IsFlat F) (n : ℤ) (hn : n ≠ 0) : Mono (n • 𝟙 F) := by
  have := mono_zsmul_id_tensorUnit.{u, v} (X := X) n hn
  have : (tensorRight F).PreservesMonomorphisms := hF
  have h : Mono ((tensorRight F).map (n • 𝟙 (𝟙_ _))) := inferInstance
  rw [Functor.map_zsmul, (tensorRight F).map_id] at h
  exact mono_zsmul_id_of_iso (λ_ F).symm n

/-- **An abelian étale sheaf is flat exactly when it is torsion-free**, i.e. when multiplication
by every nonzero integer on it is a monomorphism. -/
theorem isFlat_iff_mono_zsmul (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsFlat F ↔ ∀ n : ℤ, n ≠ 0 → Mono (n • 𝟙 F) :=
  ⟨fun hF n hn ↦ mono_zsmul_of_isFlat hF n hn, isFlat_of_mono_zsmul⟩

/-- **A subsheaf of a flat abelian étale sheaf is flat.** -/
theorem IsFlat.of_mono {F' F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    (i : F' ⟶ F) [Mono i] (hF : IsFlat F) : IsFlat F' := by
  rw [isFlat_iff_mono_zsmul] at hF ⊢
  intro n hn
  have := hF n hn
  have h : (n • 𝟙 F') ≫ i = i ≫ (n • 𝟙 F) := by
    simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  have : Mono ((n • 𝟙 F') ≫ i) := by
    rw [h]
    infer_instance
  exact mono_of_mono _ i

/-- A zero abelian étale sheaf is flat. -/
theorem isFlat_of_isZero {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    (hF : IsZero F) : IsFlat F :=
  (isFlat_iff_mono_zsmul F).2 fun _ _ ↦ hF.mono _

/-- **A direct sum of two flat abelian étale sheaves is flat.** -/
theorem isFlat_biprod {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    (hA : IsFlat A) (hB : IsFlat B) : IsFlat.{u, v} (A ⊞ B) := by
  refine (isFlat_iff_mono_zsmul _).2 fun n hn ↦ ?_
  have := mono_zsmul_of_isFlat hA n hn
  have := mono_zsmul_of_isFlat hB n hn
  have h : n • 𝟙 (A ⊞ B) = biprod.map (n • 𝟙 A) (n • 𝟙 B) := by
    apply biprod.hom_ext <;> simp [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  rw [h]
  infer_instance

/-- **The sheafification of a presheaf of torsion-free abelian groups is flat.** -/
theorem isFlat_presheafToSheaf_obj (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})
    (hP : ∀ (U : X.Etaleᵒᵖ) (n : ℤ), n ≠ 0 → Mono (n • 𝟙 (P.obj U))) :
    IsFlat ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj P) :=
  (isFlat_iff_mono_zsmul _).2 fun n hn ↦ mono_zsmul_presheafToSheaf_obj P n (fun U ↦ hP U n hn)

/-- **The constant sheaf of a torsion-free abelian group is flat.** -/
theorem isFlat_constantSheaf (A : AddCommGrpCat.{max (u + 1) v})
    (hA : ∀ n : ℤ, n ≠ 0 → Mono (n • 𝟙 A)) :
    IsFlat ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A) :=
  isFlat_presheafToSheaf_obj _ fun _ n hn ↦ hA n hn

/-! ### Colimits -/

/-- Tensoring on the left by a fixed abelian étale sheaf preserves colimits. -/
instance preservesColimitsOfSize_tensorLeft
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    PreservesColimitsOfSize.{max (u + 1) v, max (u + 1) v} (tensorLeft F) := by
  letI := isMonoidal_W_smallEtale.{u, v} X
  exact Sheaf.preservesColimitsOfSize_tensorLeft X.smallEtaleTopology F

/-- Tensoring on the right by a fixed abelian étale sheaf preserves colimits. -/
instance preservesColimitsOfSize_tensorRight
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    PreservesColimitsOfSize.{max (u + 1) v, max (u + 1) v} (tensorRight F) := by
  letI := isMonoidal_W_smallEtale.{u, v} X
  exact Sheaf.preservesColimitsOfSize_tensorRight X.smallEtaleTopology F

/-- Tensoring on the left by a fixed abelian étale sheaf preserves sequential colimits. -/
instance preservesColimitsOfShape_nat_tensorLeft
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    PreservesColimitsOfShape ℕ (tensorLeft F) := by
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft F) :=
    preservesColimitsOfSize_shrink.{0, max (u + 1) v, 0, max (u + 1) v} _
  infer_instance

section

open scoped AlgebraicGeometry.Scheme.SmallEtaleColimits

/-- **Sequential colimits of abelian étale sheaves are exact.** -/
instance hasExactColimitsOfShape_nat :
    HasExactColimitsOfShape ℕ (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) := by
  have : AB5OfSize.{0, 0} AddCommGrpCat.{max (u + 1) v} := AB5OfSize_shrink _
  have : HasExactColimitsOfShape ℕ AddCommGrpCat.{max (u + 1) v} := AB5OfSize.ofShape ℕ
  exact Sheaf.hasExactColimitsOfShape _

end

/-- **A colimit of flat abelian étale sheaves is flat**, along any shape whose colimits of
abelian étale sheaves exist and are exact: multiplication by `n` on the colimit is the colimit
of the multiplications by `n`. -/
theorem isFlat_colimit {J : Type*} [Category J]
    [HasColimitsOfShape J (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExactColimitsOfShape J (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (D : J ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hD : ∀ j, IsFlat (D.obj j)) : IsFlat (colimit D) := by
  refine (isFlat_iff_mono_zsmul _).2 fun n hn ↦ ?_
  have h : n • 𝟙 (colimit D) = colim.map (n • 𝟙 D) := by
    refine colimit.hom_ext fun j ↦ ?_
    simp [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  have : Mono (n • 𝟙 D) := by
    have (j : J) : Mono ((n • 𝟙 D).app j) := mono_zsmul_of_isFlat (hD j) n hn
    exact NatTrans.mono_of_mono_app _
  rw [h]
  infer_instance

section

open scoped AlgebraicGeometry.Scheme.SmallEtaleColimits

/-- **A sequential colimit of flat abelian étale sheaves is flat.** -/
theorem isFlat_colimit_nat (D : ℕ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hD : ∀ j, IsFlat (D.obj j)) : IsFlat (colimit D) :=
  isFlat_colimit D hD

end

/-- **A direct sum of flat abelian étale sheaves is flat.** -/
theorem isFlat_sigma {ι : Type (max (u + 1) v)}
    [HasColimitsOfShape (Discrete ι) (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (hF : ∀ i, IsFlat (F i)) :
    IsFlat (∐ F) :=
  have := Sheaf.hasExactColimitsOfShape (K := Discrete ι) X.smallEtaleTopology
    (A := AddCommGrpCat.{max (u + 1) v})
  isFlat_colimit (Discrete.functor F) fun i ↦ hF i.as

/-- **Every abelian étale sheaf is a quotient of a flat one**: of the sheafification of the
presheaf of free abelian groups on its sections. -/
theorem exists_epi_isFlat (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    ∃ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (p : F ⟶ G),
      IsFlat F ∧ Epi p := by
  let L := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}
  let P := G.obj ⋙ forget AddCommGrpCat ⋙ AddCommGrpCat.free
  let q : P ⟶ G.obj := Functor.whiskerLeft G.obj AddCommGrpCat.adj.counit
  have : Epi q := by
    have (U : X.Etaleᵒᵖ) : Epi (q.app U) := by
      dsimp [q]
      infer_instance
    exact NatTrans.epi_of_epi_app _
  refine ⟨L.obj P, L.map q ≫ (sheafificationAdjunction _ _).counit.app G, ?_, inferInstance⟩
  refine isFlat_presheafToSheaf_obj P fun U n hn ↦ ?_
  rw [AddCommGrpCat.mono_iff_injective]
  intro x y hxy
  change FreeAbelianGroup (G.obj.obj U) at x y
  exact smul_right_injective (FreeAbelianGroup (G.obj.obj U)) hn hxy

/-! ### Exactness -/

/-- **Tensoring on the right with a flat abelian étale sheaf is exact.** -/
theorem IsFlat.preservesFiniteLimits_tensorRight
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (hF : IsFlat F) :
    PreservesFiniteLimits (tensorRight F) := by
  have : (tensorRight F).PreservesMonomorphisms := hF
  exact Stacks.Sites.AbelianLowerShriek.preservesFiniteLimits_of_preservesMonomorphisms _

/-- **Tensoring on the left with a flat abelian étale sheaf is exact.** -/
theorem IsFlat.preservesFiniteLimits_tensorLeft
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (hF : IsFlat F) :
    PreservesFiniteLimits (tensorLeft F) := by
  have : (tensorLeft F).PreservesMonomorphisms :=
    preservesMonomorphisms_tensorLeft_of_mono_zsmul ((isFlat_iff_mono_zsmul F).1 hF)
  exact Stacks.Sites.AbelianLowerShriek.preservesFiniteLimits_of_preservesMonomorphisms _

/-- **Tensoring a short exact sequence on the right by a flat abelian étale sheaf gives a short
exact sequence.** -/
theorem IsFlat.shortExact_map_tensorRight
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (hF : IsFlat F)
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.ShortExact) : (S.map (tensorRight F)).ShortExact :=
  have := hF.preservesFiniteLimits_tensorRight
  hS.map_of_exact _

/-- **Tensoring a short exact sequence on the left by a flat abelian étale sheaf gives a short
exact sequence.** -/
theorem IsFlat.shortExact_map_tensorLeft
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (hF : IsFlat F)
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.ShortExact) : (S.map (tensorLeft F)).ShortExact :=
  have := hF.preservesFiniteLimits_tensorLeft
  hS.map_of_exact _

/-- **Tensoring an acyclic complex termwise on the right by a flat abelian étale sheaf gives
an acyclic complex.** -/
theorem IsFlat.acyclic_map_tensorRight
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (hF : IsFlat F)
    {ι : Type*} {c : ComplexShape ι}
    {K : HomologicalComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c}
    (hK : K.Acyclic) : (((tensorRight F).mapHomologicalComplex c).obj K).Acyclic :=
  have := hF.preservesFiniteLimits_tensorRight
  HomologicalComplex.Acyclic.map _ hK

/-- **Tensoring an acyclic complex termwise on the left by a flat abelian étale sheaf gives
an acyclic complex.** -/
theorem IsFlat.acyclic_map_tensorLeft
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (hF : IsFlat F)
    {ι : Type*} {c : ComplexShape ι}
    {K : HomologicalComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c}
    (hK : K.Acyclic) : (((tensorLeft F).mapHomologicalComplex c).obj K).Acyclic :=
  have := hF.preservesFiniteLimits_tensorLeft
  HomologicalComplex.Acyclic.map _ hK

end Stacks.EtaleCohomology

end
