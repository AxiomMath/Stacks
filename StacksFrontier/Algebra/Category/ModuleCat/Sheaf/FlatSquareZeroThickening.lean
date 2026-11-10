module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.EpiMono
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverTensorExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor
import StacksCore.Tactic.StacksAttribute

attribute [local instance] Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits

/-!
# Flat modules over a square-zero thickening

Let `O' ⟶ O` be a locally surjective morphism of sheaves of commutative
rings whose kernel `I` has square zero.  An `O'`-module `F'` is flat if and
only if its reduction `F = F' / IF'` is flat over `O` and the canonical map
`I ⊗[O] F ⟶ F'` is a monomorphism.

The ideal, the reduction and the two multiplication maps enter the statement through their
universal and sectionwise characterizing properties: the reduction is a cokernel of the
multiplication map, and the multiplication maps are determined by their values on pure tensors.

## Main definitions

* `Stacks.SheafOfModules.FlatSquareZero.multiplicationMap`: the multiplication map
  `I ⊗[O'] G ⟶ G` of a sheaf of `O'`-modules `G`.
* `Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap`: the comparison map
  `B ⊗[O'] G ⟶ B ⊗[O] F` induced by a morphism `G ⟶ F` to an `O`-module.

## Main results

* `Stacks.SheafOfModules.FlatSquareZero.isFlat_iff_reduction_isFlat_and_multiplication_mono`:
  `F'` is flat if and only if `F` is flat and `I ⊗[O] F ⟶ F'` is a monomorphism.
* `Stacks.SheafOfModules.FlatSquareZero.exists_reduction_and_multiplicationMaps`: the
  reduction and the two multiplication maps exist.
* `Stacks.SheafOfModules.FlatSquareZero.multiplicationMap_unique`: a multiplication map is
  determined by its values on pure tensors.

## References

* [Stacks Project, Tag 08M4](https://stacks.math.columbia.edu/tag/08M4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open TensorProduct

universe v u w

namespace Stacks.SheafOfModules.FlatSquareZero

private lemma isPullback_of_exact_of_mono
    {D : Type*} [Category D] [Abelian D]
    {S T : ShortComplex D} (φ : S ⟶ T)
    (hS : S.Exact) [Mono S.f] [Mono T.f] [Mono φ.τ₃] :
    IsPullback S.f φ.τ₁ φ.τ₂ T.f := by
  apply IsPullback.mk' φ.comm₁₂.symm
  · intro W a b h _
    exact (cancel_mono S.f).mp h
  · intro W a b h
    have hz : a ≫ S.g = 0 := by
      apply (cancel_mono φ.τ₃).mp
      rw [Category.assoc, ← φ.comm₂₃, ← Category.assoc, h, Category.assoc, T.zero,
        Limits.comp_zero, Limits.zero_comp]
    let k := hS.lift a hz
    refine ⟨k, hS.lift_f a hz, ?_⟩
    apply (cancel_mono T.f).mp
    rw [Category.assoc, φ.comm₁₂, ← Category.assoc, hS.lift_f]
    exact h

private lemma mono_cokernelMap_of_exact_of_mono
    {D : Type*} [Category D] [Abelian D]
    {S T : ShortComplex D} (φ : S ⟶ T)
    (hS : S.Exact) [Mono T.f] [Mono φ.τ₃] :
    Mono (cokernel.map φ.τ₁ φ.τ₂ S.f T.f φ.comm₁₂) := by
  apply Preadditive.mono_of_cancel_zero
  intro W z hz
  obtain ⟨W₁, e₁, he₁, x, hx⟩ :=
    (epi_iff_surjective_up_to_refinements (cokernel.π φ.τ₁)).mp inferInstance z
  have hm : cokernel.π φ.τ₁ ≫ cokernel.map φ.τ₁ φ.τ₂ S.f T.f φ.comm₁₂ =
      T.f ≫ cokernel.π φ.τ₂ := cokernel.π_desc _ _ _
  have hx₀ : (x ≫ T.f) ≫ cokernel.π φ.τ₂ = 0 := by
    rw [Category.assoc, ← hm, ← Category.assoc, ← hx,
      Category.assoc, hz, Limits.comp_zero]
  let K := ShortComplex.mk φ.τ₂ (cokernel.π φ.τ₂) (cokernel.condition φ.τ₂)
  obtain ⟨W₂, e₂, he₂, y, hy⟩ :=
    (K.exact_of_g_is_cokernel (cokernelIsCokernel φ.τ₂)).exact_up_to_refinements
      (x ≫ T.f) hx₀
  have hy₀ : y ≫ S.g = 0 := by
    apply (cancel_mono φ.τ₃).mp
    rw [Category.assoc, ← φ.comm₂₃, ← Category.assoc, ← hy,
      Category.assoc, Category.assoc, T.zero, Limits.comp_zero, Limits.comp_zero,
      Limits.zero_comp]
  obtain ⟨W₃, e₃, he₃, a, ha⟩ := hS.exact_up_to_refinements y hy₀
  have hx' : e₃ ≫ e₂ ≫ x = a ≫ φ.τ₁ := by
    apply (cancel_mono T.f).mp
    simp only [Category.assoc]
    rw [hy, ← Category.assoc, ha, Category.assoc, ← φ.comm₁₂]
  apply (cancel_epi e₁).mp
  apply (cancel_epi e₂).mp
  apply (cancel_epi e₃).mp
  simp only [Limits.comp_zero]
  rw [hx]
  calc
    e₃ ≫ e₂ ≫ x ≫ cokernel.π φ.τ₁ =
        (e₃ ≫ e₂ ≫ x) ≫ cokernel.π φ.τ₁ := by simp only [Category.assoc]
    _ = (a ≫ φ.τ₁) ≫ cokernel.π φ.τ₁ := by rw [hx']
    _ = 0 := by simp only [Category.assoc, cokernel.condition, Limits.comp_zero]

private lemma mono_of_mono_cokernelMap
    {D : Type*} [Category D] [Abelian D]
    {A B A' B' Q Q' : D} {l : A ⟶ B} {l' : A' ⟶ B'}
    {a : A ⟶ A'} {b : B ⟶ B'} (w : l ≫ b = a ≫ l')
    (p : B ⟶ Q) (p' : B' ⟶ Q') (h : Q ⟶ Q')
    (hp : l ≫ p = 0) (hp' : l' ≫ p' = 0)
    (hP : IsColimit (CokernelCofork.ofπ p hp))
    (hP' : IsColimit (CokernelCofork.ofπ p' hp'))
    (comm : p ≫ h = b ≫ p')
    [Mono (cokernel.map l l' a b w)] : Mono h := by
  let e := (cokernelIsCokernel l).coconePointUniqueUpToIso hP
  let e' := (cokernelIsCokernel l').coconePointUniqueUpToIso hP'
  let m := cokernel.map l l' a b w
  have he : cokernel.π l ≫ e.hom = p :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel l) hP
      WalkingParallelPair.one
  have he' : cokernel.π l' ≫ e'.hom = p' :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel l') hP'
      WalkingParallelPair.one
  have hm : e.hom ≫ h = m ≫ e'.hom := by
    apply (cancel_epi (cokernel.π l)).mp
    rw [← Category.assoc, he, comm, ← Category.assoc, cokernel.π_desc,
      Category.assoc, he']
  have : Mono (e.hom ≫ h) := by rw [hm]; infer_instance
  exact (mono_comp_iff_of_isIso e.hom h).mp this

private lemma mono_of_cokernel_diagram_of_isPullback
    {D : Type*} [Category D] [Abelian D]
    {A B A' B' Q Q' : D} {l : A ⟶ B} {l' : A' ⟶ B'}
    {a : A ⟶ A'} {b : B ⟶ B'} (hsq : IsPullback a l l' b)
    (p : B ⟶ Q) (p' : B' ⟶ Q') (h : Q ⟶ Q')
    (hp : l ≫ p = 0) (hp' : l' ≫ p' = 0)
    (hP : IsColimit (CokernelCofork.ofπ p hp))
    (hP' : IsColimit (CokernelCofork.ofπ p' hp'))
    (comm : p ≫ h = b ≫ p') : Mono h :=
  have : Mono (cokernel.map l l' a b hsq.w.symm) :=
    Abelian.mono_cokernel_map_of_isPullback hsq.flip
  mono_of_mono_cokernelMap hsq.w.symm p p' h hp hp' hP hP' comm

/-- The underlying morphism of presheaves of a monomorphism of sheaves of modules is a
monomorphism. -/
private lemma mono_val_of_mono
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {M N : SheafOfModules.{w} R} (g : M ⟶ N) [Mono g] :
    Mono g.val := by
  have : PreservesFiniteLimits (SheafOfModules.forget.{w} R) :=
    SheafOfModules.Finite.forgetPreservesFiniteLimits _
  exact Functor.map_mono (SheafOfModules.forget.{w} R) g

private theorem flat_tensor_preserves_mono
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    (O : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat F)
    {G H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (g : G ⟶ H) [Mono g] :
    Mono ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F)).map g) := by
  have : PreservesFiniteLimits
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F)) :=
    (exactFunctor_iff
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F))).mp hF |>.1
  exact Functor.map_mono _ g

/-- The sheafification hom equivalence is the hom equivalence of the sheafification adjunction. -/
private lemma sheafificationHomEquiv_eq_homEquiv
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    {R₀ : Cᵒᵖ ⥤ RingCat.{w}} {R : Sheaf J RingCat.{w}} (α : R₀ ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    (P : PresheafOfModules.{w} R₀) (N : SheafOfModules.{w} R) :
    PresheafOfModules.sheafificationHomEquiv α (P := P) (F := N) =
      (PresheafOfModules.sheafificationAdjunction α).homEquiv P N :=
  Equiv.ext fun g => (PresheafOfModules.sheafificationAdjunction_homEquiv_apply _ g).symm

/-- Tensoring on the left with a sheaf of `O`-modules preserves colimits. -/
private lemma tensorLeft_preservesColimits
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    PreservesColimitsOfSize.{0, 0}
      ((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj G) :=
  preservesColimitsOfSize_shrink.{0, w, 0, w} _

/-- Tensoring on the left with a sheaf of `O`-modules preserves epimorphisms. -/
private lemma epi_tensorLeft_map
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (g : A ⟶ B) [Epi g] :
    Epi (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj G).map g) := by
  have := tensorLeft_preservesColimits O G
  infer_instance

/-- Tensoring a short exact sequence on the left with `N` gives a cokernel cofork for `g`. -/
private noncomputable def isColimit_map_tensorLeft
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    (O : Sheaf J CommRingCat.{w})
    {S : ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))}
    (hS : S.ShortExact)
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    IsColimit (CokernelCofork.ofπ
      (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj N).map S.g)
      (S.map ((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj N)).zero) := by
  have := tensorLeft_preservesColimits O N
  have := hS.epi_g
  have : Epi (S.map ((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj N)).g :=
    epi_tensorLeft_map O N S.g
  exact (hS.exact.map_of_epi_of_preservesCokernel
    ((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj N) hS.epi_g
      inferInstance).gIsCokernel

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The underlying morphism of sheaves of rings of a morphism of sheaves of
commutative rings. -/
public abbrev ringMap {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O) :
    Stacks.SheafOfModules.Tensor.ringSheaf O' ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf O :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).map f

/-- The natural isomorphism between tensoring with `G` on the left and tensoring with `G` on the
right, as endofunctors of sheaves of `O`-modules. -/
noncomputable def tensorLeftIsoTensorRight
    (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj G ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G) := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf O
  letI : SymmetricCategory (PresheafOfModules.{w} R.obj) :=
    PresheafOfModulesOfCommRing.symmetricCategory (R := O.obj)
  exact Functor.isoWhiskerLeft (SheafOfModules.forget R)
    (Functor.isoWhiskerRight
      (BraidedCategory.tensorLeftIsoTensorRight G.val)
      (PresheafOfModules.sheafification (𝟙 R.obj)))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Tensoring on the right with a sheaf of `O`-modules preserves finite colimits. -/
lemma tensorRight_preservesFiniteColimits
    (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    PreservesFiniteColimits
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G)) := by
  have := tensorLeft_preservesColimits O G
  exact preservesFiniteColimits_of_natIso (tensorLeftIsoTensorRight O G)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Tensoring on the right with a sheaf of `O`-modules is an additive functor. -/
lemma tensorRight_additive
    (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G)).Additive := by
  apply rightExactFunctor_le_additiveFunctor _ _ _
  exact (rightExactFunctor_iff _).mpr (tensorRight_preservesFiniteColimits O G)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Tensoring on the left with a sheaf of `O`-modules is an additive functor. -/
lemma tensorLeft_additive
    (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj G).Additive := by
  have := tensorLeft_preservesColimits O G
  apply rightExactFunctor_le_additiveFunctor _ _ _
  exact (rightExactFunctor_iff _).mpr inferInstance

attribute [local instance] tensorRight_preservesFiniteColimits
  tensorRight_additive tensorLeft_additive

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
private lemma isFlat_of_tensorRight_preservesMonomorphisms
    (O : Sheaf J CommRingCat.{w})
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (h : ∀ {A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
      (g : A ⟶ B) [Mono g],
        Mono ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G)).map g)) :
    AlgebraicGeometry.SheafOfModules.IsFlat G := by
  let T := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G)
  rw [AlgebraicGeometry.SheafOfModules.IsFlat, exactFunctor_iff]
  refine ⟨?_, inferInstance⟩
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono T).mpr
  intro S hS
  have : Mono S.f := hS.mono_f
  exact ⟨hS.exact.map_of_epi_of_preservesCokernel T hS.epi_g inferInstance,
    h S.f⟩

private lemma tensorLeft_map_mono_of_shortExact
    (O : Sheaf J CommRingCat.{w})
    {L P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (l : L ⟶ P)
    (hP : AlgebraicGeometry.SheafOfModules.IsFlat P)
    (S : ShortComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (hS : S.ShortExact)
    (h₁ : Mono (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj S.X₁).map l))
    (h₃ : Mono (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj S.X₃).map l)) :
    Mono (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj S.X₂).map l) := by
  let TL := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj L)
  let TP := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj P)
  let t := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.map l
  have : Mono S.f := hS.mono_f
  exact ShortComplex.mono_of_mono_of_mono_of_mono (S.mapNatTrans t)
    (hS.exact.map_of_epi_of_preservesCokernel TL hS.epi_g inferInstance)
    (flat_tensor_preserves_mono O P hP S.f) h₁ h₃

private lemma isFlat_of_pure_presentation
    (O : Sheaf J CommRingCat.{w})
    (S : ShortComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (hS : S.ShortExact) (hP : AlgebraicGeometry.SheafOfModules.IsFlat S.X₂)
    (hmono : ∀ N : SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf O),
      Mono (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj N).map S.f)) :
    AlgebraicGeometry.SheafOfModules.IsFlat S.X₃ := by
  apply isFlat_of_tensorRight_preservesMonomorphisms O S.X₃
  intro A B α hα
  let L := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj S.X₁)
  let P := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj S.X₂)
  let T := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj S.X₃)
  let l := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.map S.f
  let p := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.map S.g
  have hPα : Mono (P.map α) := flat_tensor_preserves_mono O S.X₂ hP α
  let E := ShortComplex.mk α (cokernel.π α) (cokernel.condition α)
  have hE : E.ShortExact := ⟨E.exact_of_g_is_cokernel (cokernelIsCokernel α)⟩
  have hLE : (E.map L).Exact := hE.exact.map_of_epi_of_preservesCokernel L
    hE.epi_g inferInstance
  have hlA : Mono (l.app A) := hmono A
  have hLα : Mono (L.map α) := mono_of_mono_fac (l.naturality α)
  let φ : E.map L ⟶ E.map P := E.mapNatTrans l
  have : Mono (E.map L).f := hLα
  have : Mono (E.map P).f := hPα
  have : Mono φ.τ₃ := hmono _
  have hpb := isPullback_of_exact_of_mono φ hLE
  exact mono_of_cokernel_diagram_of_isPullback hpb
    (p.app A) (p.app B) (T.map α)
    (S.map ((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj A)).zero
    (S.map ((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj B)).zero
    (isColimit_map_tensorLeft O hS A) (isColimit_map_tensorLeft O hS B) (p.naturality α).symm

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
private lemma kernelMap_mono
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hi_zero : ∀ (U : Cᵒᵖ) (a : I.val.obj U),
      f.hom.app U (show O'.obj.obj U from i.val.app U a) = 0)
    (hi_univ : ∀ (U : Cᵒᵖ) (x : O'.obj.obj U), f.hom.app U x = 0 →
      ∃! a : I.val.obj U, (show O'.obj.obj U from i.val.app U a) = x) : Mono i := by
  have : (SheafOfModules.forget.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')).Faithful :=
    (SheafOfModules.fullyFaithfulForget (Stacks.SheafOfModules.Tensor.ringSheaf O')).faithful
  have hval : Mono i.val := by
    apply PresheafOfModules.mono_of_injective
    intro U x y hxy
    let x' : I.val.obj U := x
    let y' : I.val.obj U := y
    have hxy' : i.val.app U x' = i.val.app U y' := by simpa [x', y'] using hxy
    obtain ⟨a, ha, ha_unique⟩ := hi_univ U (i.val.app U x') (hi_zero U x')
    exact (ha_unique x' rfl).trans (ha_unique y' hxy'.symm).symm
  exact (SheafOfModules.forget
    (Stacks.SheafOfModules.Tensor.ringSheaf O')).mono_of_mono_map hval

private def quotientKerPresheaf {R S : Sheaf J RingCat.{w}} (α : R ⟶ S) :
    Cᵒᵖ ⥤ RingCat.{w} where
  obj U := RingCat.of (R.obj.obj U ⧸ RingHom.ker (α.hom.app U).hom)
  map {U V} f := RingCat.ofHom (Ideal.Quotient.lift _
    ((Ideal.Quotient.mk _).comp (R.obj.map f).hom) (by
      intro a ha
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change (α.hom.app V) (R.obj.map f a) = 0
      have h := ConcreteCategory.congr_hom (α.hom.naturality f) a
      dsimp at h
      rw [h, show α.hom.app U a = 0 from ha, map_zero]))
  map_id U := by
    ext a
    change Ideal.Quotient.mk _ (R.obj.map (𝟙 U) a) = _
    simp
  map_comp f g := by
    ext a
    change Ideal.Quotient.mk _ (R.obj.map (f ≫ g) a) = _
    simp [Functor.map_comp]

private def quotientKerInclusion {R S : Sheaf J RingCat.{w}} (α : R ⟶ S) :
    quotientKerPresheaf α ⟶ S.obj where
  app U := RingCat.ofHom (α.hom.app U).hom.kerLift
  naturality {U V} f := by
    ext a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ConcreteCategory.congr_hom (α.hom.naturality f) a

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
private lemma quotientKerInclusion_injective {R S : Sheaf J RingCat.{w}}
    (α : R ⟶ S) (U : Cᵒᵖ) :
    Function.Injective ((quotientKerInclusion α).app U) :=
  (α.hom.app U).hom.kerLift_injective

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
private lemma quotientKerInclusion_locallySurjective
    {R S : Sheaf J RingCat.{w}} (α : R ⟶ S)
    [Presheaf.IsLocallySurjective J α.hom] :
    Presheaf.IsLocallySurjective J (quotientKerInclusion α) := by
  constructor
  intro U x
  apply J.superset_covering _ (Presheaf.imageSieve_mem J α.hom x)
  rintro V f ⟨a, ha⟩
  exact ⟨Ideal.Quotient.mk _ a, ha⟩

private noncomputable def descendModule
    {R S : Sheaf J RingCat.{w}} (α : R ⟶ S)
    [Presheaf.IsLocallySurjective J α.hom]
    (M : SheafOfModules.{w} R)
    (hM : ∀ (U : Cᵒᵖ) (a : R.obj.obj U), α.hom.app U a = 0 →
      ∀ m : M.val.obj U, a • m = 0) :
    Σ N : SheafOfModules.{w} S, (SheafOfModules.restrictScalars α).obj N ≅ M := by
  let hT (U : Cᵒᵖ) : Module.IsTorsionBySet (R.obj.obj U) (M.val.obj U)
      (RingHom.ker (α.hom.app U).hom) := fun m a => hM U a a.property m
  letI (U : Cᵒᵖ) : Module ((quotientKerPresheaf α).obj U) (M.val.presheaf.obj U) :=
    (hT U).module
  let M₀ : PresheafOfModules.{w} (quotientKerPresheaf α) :=
    PresheafOfModules.ofPresheaf M.val.presheaf (by
      intro U V f a m
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact M.val.map_smul f a m)
  letI : Presheaf.IsLocallyInjective J (quotientKerInclusion α) :=
    Presheaf.isLocallyInjective_of_injective J _ (quotientKerInclusion_injective α)
  letI : Presheaf.IsLocallySurjective J (quotientKerInclusion α) :=
    quotientKerInclusion_locallySurjective α
  let A : Sheaf J AddCommGrpCat.{w} := (SheafOfModules.toSheaf R).obj M
  let φ₀ : M₀.presheaf ⟶ A.obj := 𝟙 M.val.presheaf
  letI : Presheaf.IsLocallyInjective J φ₀ :=
    inferInstanceAs (Presheaf.IsLocallyInjective J (𝟙 M.val.presheaf))
  letI : Presheaf.IsLocallySurjective J φ₀ :=
    inferInstanceAs (Presheaf.IsLocallySurjective J (𝟙 M.val.presheaf))
  let N := PresheafOfModules.sheafify (quotientKerInclusion α) (M₀ := M₀) (A := A) φ₀
  have hm (U : Cᵒᵖ) (r : R.obj.obj U) (m : M.val.obj U) :
      (α.hom.app U r) • (show N.val.obj U from m) = r • m := by
    exact (((PresheafOfModules.toSheafify (quotientKerInclusion α)
      (M₀ := M₀) (A := A) φ₀).app U).hom.map_smul
      (Ideal.Quotient.mk _ r) m).symm
  refine ⟨N, ?_⟩
  refine {
    hom := ⟨PresheafOfModules.homMk (𝟙 M.val.presheaf) ?_⟩
    inv := ⟨PresheafOfModules.homMk (𝟙 M.val.presheaf) ?_⟩
    hom_inv_id := by ext; rfl
    inv_hom_id := by ext; rfl }
  · exact hm
  · exact fun U r m ↦ (hm U r m).symm

private noncomputable def quotientUnitMap
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O) :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O') ⟶
      (SheafOfModules.restrictScalars (ringMap f)).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) := by
  let M := (SheafOfModules.restrictScalars (ringMap f)).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
  let s : M.sections := PresheafOfModules.sectionsMk
    (fun U ↦ (1 : O.obj.obj U)) (by
      intro U V g
      change (O.obj.map g).hom 1 = 1
      exact (O.obj.map g).hom.map_one)
  exact (SheafOfModules.unitHomEquiv M).symm s

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
private lemma quotientUnitMap_app
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (U : Cᵒᵖ) (x : O'.obj.obj U) :
    (quotientUnitMap f).val.app U x = f.hom.app U x := by
  change (f.hom.app U x) * (1 : O.obj.obj U) = f.hom.app U x
  exact mul_one _

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
private lemma kernelMap_comp_quotientUnitMap
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hi_zero : ∀ (U : Cᵒᵖ) (a : I.val.obj U),
      f.hom.app U (show O'.obj.obj U from i.val.app U a) = 0) :
    i ≫ quotientUnitMap f = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext a
  change (quotientUnitMap f).val.app U (i.val.app U a) = 0
  exact (quotientUnitMap_app f U _).trans (hi_zero U (show I.val.obj U from a))

/-- The morphism of presheaves of `O'`-modules `I ⊗ G ⟶ G` sending `a ⊗ x` to `i a • x`. -/
noncomputable def multiplicationPresheafMap
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O')) :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj
      ((SheafOfModules.restrictScalars (ringMap f)).obj I).val G.val ⟶ G.val where
  app U := by
    let R := O'.obj.obj U
    letI : CommSemiring R := inferInstanceAs (CommSemiring (O'.obj.obj U))
    exact ModuleCat.MonoidalCategory.tensorLift
      (fun a x => (show R from (i.val.app U).hom a) • x)
      (by
        intro a b x
        have h : (i.val.app U).hom (a + b) =
            (i.val.app U).hom a + (i.val.app U).hom b := map_add _ _ _
        change (show R from (i.val.app U).hom (a + b)) • x = _
        rw [h]
        exact add_smul _ _ _)
      (by
        intro r a x
        let S := (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U
        have h : (show R from (i.val.app U).hom (r • a)) =
            (show R from r) * (show R from (i.val.app U).hom a) :=
          map_smul (i.val.app U).hom (show S from r) a
        change (show R from (i.val.app U).hom (r • a)) • x = _
        rw [h]
        change O'.obj.obj U at r
        let ia : R := (i.val.app U).hom a
        change (r * ia) • x = r • (ia • x)
        exact mul_smul _ _ _)
      (by intro a x y; exact smul_add _ _ _)
      (by
        intro r a x
        change O'.obj.obj U at r
        change (show O'.obj.obj U from (i.val.app U).hom a) • (r • x) =
          r • ((show O'.obj.obj U from (i.val.app U).hom a) • x)
        exact smul_comm _ _ _)
  naturality {U V} g := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a x
    have key : (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj V from
        (i.val.app V).hom (((SheafOfModules.restrictScalars (ringMap f)).obj I).val.map g a)) =
        (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.map g
          (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
            (i.val.app U).hom a) :=
      PresheafOfModules.naturality_apply i.val g a
    change (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj V from
        (i.val.app V).hom (((SheafOfModules.restrictScalars (ringMap f)).obj I).val.map g a)) •
        (show G.val.obj V from G.val.map g x) =
      G.val.map g
        ((show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
          (i.val.app U).hom a) • x)
    rw [key]
    exact (PresheafOfModules.map_smul G.val g _ x).symm
omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
private lemma multiplicationPresheafMap_natural
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {G H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')}
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (α : G ⟶ H) :
    multiplicationPresheafMap f I G i ≫ α.val =
      MonoidalCategory.whiskerLeft
        ((SheafOfModules.restrictScalars (ringMap f)).obj I).val α.val ≫
          multiplicationPresheafMap f I H i := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a x
  change α.val.app U ((show
      (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
      (i.val.app U).hom a) • x) =
    (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
      (i.val.app U).hom a) • α.val.app U x
  exact (α.val.app U).hom.map_smul _ _
omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
private lemma multiplicationPresheafMap_sq_zero
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hsq : ∀ (U : Cᵒᵖ) (a b : I.val.obj U),
      (show O'.obj.obj U from i.val.app U a) *
        (show O'.obj.obj U from i.val.app U b) = 0) :
    MonoidalCategory.whiskerLeft
        ((SheafOfModules.restrictScalars (ringMap f)).obj I).val
        (multiplicationPresheafMap f I G i) ≫
      multiplicationPresheafMap f I G i = 0 := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext₃
  intro a b x
  have h : (show O'.obj.obj U from i.val.app U a) *
      (show O'.obj.obj U from i.val.app U b) = 0 := hsq U a b
  change (show O'.obj.obj U from i.val.app U a) •
    ((show O'.obj.obj U from i.val.app U b) • x) = 0
  exact (smul_smul _ _ x).trans
    ((congrArg (fun c => c • x) h).trans (zero_smul _ x))
private noncomputable def nestedMultiplicationMap
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O')) :
    (PresheafOfModules.sheafification
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).obj
      (MonoidalCategoryStruct.tensorObj
        ((SheafOfModules.restrictScalars (ringMap f)).obj I).val
        (MonoidalCategoryStruct.tensorObj
          ((SheafOfModules.restrictScalars (ringMap f)).obj I).val G.val)) ⟶ G := by
  let A := ((SheafOfModules.restrictScalars (ringMap f)).obj I).val
  let P := MonoidalCategoryStruct.tensorObj A (MonoidalCategoryStruct.tensorObj A G.val)
  let n : P ⟶ G.val :=
    MonoidalCategory.whiskerLeft A (multiplicationPresheafMap f I G i) ≫
      multiplicationPresheafMap f I G i
  exact (PresheafOfModules.sheafificationHomEquiv
    (α := 𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)
    (P := P) (F := G)).symm n

private lemma nestedMultiplicationMap_eq_zero
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hsq : ∀ (U : Cᵒᵖ) (a b : I.val.obj U),
      (show O'.obj.obj U from i.val.app U a) *
        (show O'.obj.obj U from i.val.app U b) = 0) :
    nestedMultiplicationMap f I G i = 0 := by
  unfold nestedMultiplicationMap
  dsimp only
  let A := ((SheafOfModules.restrictScalars (ringMap f)).obj I).val
  let P := MonoidalCategoryStruct.tensorObj A (MonoidalCategoryStruct.tensorObj A G.val)
  let e := PresheafOfModules.sheafificationHomEquiv
    (α := 𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj) (P := P) (F := G)
  have he : e = (PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).homEquiv P G :=
    sheafificationHomEquiv_eq_homEquiv _ _ _
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)
  have : (SheafOfModules.forget.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')).Additive :=
    SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget _
  have : (SheafOfModules.forget.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O') ⋙
      PresheafOfModules.restrictScalars
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).Additive :=
    inferInstance
  have : (PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).Additive :=
    adj.left_adjoint_additive
  change e.symm
      (MonoidalCategory.whiskerLeft A (multiplicationPresheafMap f I G i) ≫
        multiplicationPresheafMap f I G i) = 0
  have hz : e.symm (0 : P ⟶
      (PresheafOfModules.restrictScalars
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).obj G.val) =
      0 := by
    rw [he]
    exact adj.homAddEquiv_symm_zero P G
  rw [← hz]
  exact congrArg e.symm (multiplicationPresheafMap_sq_zero f I G i hsq)

/-- The multiplication map `I ⊗[O'] G ⟶ G` of sheaves of `O'`-modules, the morphism out of the
sheafified tensor product induced by `multiplicationPresheafMap`. -/
noncomputable def multiplicationMap
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O')) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj G)).obj
        ((SheafOfModules.restrictScalars (ringMap f)).obj I) ⟶ G :=
  (PresheafOfModules.sheafificationHomEquiv
    (α := 𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)
    (P := MonoidalCategoryStruct.tensorObj
      ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O')).obj
        ((SheafOfModules.restrictScalars (ringMap f)).obj I))
      ((SheafOfModules.forget
        (Stacks.SheafOfModules.Tensor.ringSheaf O')).obj G))
    (F := G)).symm (multiplicationPresheafMap f I G i)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
private lemma sheafificationLiftUnitApply
    {R₀ : Cᵒᵖ ⥤ RingCat.{w}} {R : Sheaf J RingCat.{w}} (α : R₀ ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    (P : PresheafOfModules.{w} R₀) (N : SheafOfModules.{w} R)
    (t : P ⟶ (PresheafOfModules.restrictScalars α).obj N.val)
    (U : Cᵒᵖ) (x : P.obj U) :
    ((PresheafOfModules.sheafificationHomEquiv α).symm t).val.app U
      (((PresheafOfModules.sheafificationAdjunction α).unit.app P).app U x) =
      t.app U x :=
  congrArg (fun k => k.app U x)
    ((PresheafOfModules.sheafificationHomEquiv α).apply_symm_apply t)

/-- `multiplicationMap f I G i` sends the image of a pure tensor `a ⊗ x` to `i a • x`. -/
lemma multiplicationMap_tmul
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (U : Cᵒᵖ) (a : I.val.obj U) (x : G.val.obj U) :
    (multiplicationMap f I G i).val.app U
        (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
            Stacks.SheafOfModules.Tensor.ringSheaf
            O')
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
      (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars (ringMap f)).obj I).val
          G.val)).app U
            (a ⊗ₜ[O'.obj.obj U] x)) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
        i.val.app U a) • x :=
  (sheafificationLiftUnitApply
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)
      (MonoidalCategoryStruct.tensorObj
        ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O')).obj
          ((SheafOfModules.restrictScalars (ringMap f)).obj I))
        ((SheafOfModules.forget
          (Stacks.SheafOfModules.Tensor.ringSheaf O')).obj G))
      G (multiplicationPresheafMap f I G i) U (a ⊗ₜ[O'.obj.obj U] x)).trans rfl

/-- A morphism `I ⊗[O'] G ⟶ G` sending the image of every pure tensor `a ⊗ x` to `i a • x` is
`multiplicationMap f I G i`. -/
lemma multiplicationMap_eq_of_tmul
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (ν : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj G)).obj
        ((SheafOfModules.restrictScalars (ringMap f)).obj I) ⟶ G)
    (hν : ∀ (U : Cᵒᵖ) (a : I.val.obj U) (x : G.val.obj U),
      ν.val.app U
          (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
              Stacks.SheafOfModules.Tensor.ringSheaf
              O')
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
      (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars (ringMap f)).obj I).val
          G.val)).app U
              (a ⊗ₜ[O'.obj.obj U] x)) =
        (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
          i.val.app U a) • x) :
    ν = multiplicationMap f I G i := by
  let P := MonoidalCategoryStruct.tensorObj
    ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O')).obj
      ((SheafOfModules.restrictScalars (ringMap f)).obj I))
    ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O')).obj G)
  let e := PresheafOfModules.sheafificationHomEquiv
    (α := 𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj) (P := P) (F := G)
  apply e.injective
  have key : e ν = multiplicationPresheafMap f I G i := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a x
    exact hν U a x
  exact key.trans (e.apply_symm_apply (multiplicationPresheafMap f I G i)).symm
private noncomputable def annihilatorPresheafSubmodule
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')) :
    G.val.Submodule where
  obj U :=
    { carrier := {x | ∀ (V : Cᵒᵖ) (g : U ⟶ V) (a : I.val.obj V),
        (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj V from
            (i.val.app V).hom a) •
          G.val.map g x = 0}
      zero_mem' := by
        intro V g a
        rw [map_zero]
        exact smul_zero _
      add_mem' := by
        intro x y hx hy V g a
        rw [map_add, smul_add, hx V g a, hy V g a]
        simp
      smul_mem' := by
        intro r x hx V g a
        let : CommSemiring
            ((Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj V) :=
          inferInstanceAs (CommSemiring (O'.obj.obj V))
        change (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj V from
            (i.val.app V).hom a) •
          G.val.map g (r • x) = 0
        rw [PresheafOfModules.map_smul]
        let c : (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj V :=
          (i.val.app V).hom a
        let r' : (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj V :=
          (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.map g r
        change c • (r' • G.val.map g x) = 0
        calc
          c • (r' • G.val.map g x) = (c * r') • G.val.map g x := by rw [mul_smul]
          _ = (r' * c) • G.val.map g x :=
              congrArg (fun t => t • G.val.map g x) (mul_comm c r')
          _ = r' • (c • G.val.map g x) := by rw [mul_smul]
          _ = 0 := by rw [hx V g a]; simp }
  map {U V} g := by
    intro x hx W k a
    change (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj W from
        (i.val.app W).hom a) •
      G.val.map k (G.val.map g x) = 0
    rw [← PresheafOfModules.map_comp_apply]
    exact hx W (g ≫ k) a
omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
private lemma multiplication_mem_annihilatorPresheaf
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hsq : ∀ (U : Cᵒᵖ) (a b : I.val.obj U),
      (show O'.obj.obj U from i.val.app U a) *
        (show O'.obj.obj U from i.val.app U b) = 0)
    (U : Cᵒᵖ) (a : I.val.obj U) (x : G.val.obj U) :
    (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
      (i.val.app U).hom a) • x ∈
      (annihilatorPresheafSubmodule f I i G).obj U := by
  intro V g b
  let Iₛ := (SheafOfModules.restrictScalars (ringMap f)).obj I
  let : CommSemiring ((Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj V) :=
    inferInstanceAs (CommSemiring (O'.obj.obj V))
  let aₛ : Iₛ.val.obj U := a
  have hi : (i.val.app V).hom (Iₛ.val.map g a) =
      ((SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf O')).val.map g).hom
        ((i.val.app U).hom a) := PresheafOfModules.naturality_apply i.val g aₛ
  change (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj V from
      (i.val.app V).hom b) •
    G.val.map g
      ((show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
        (i.val.app U).hom a) • x) = 0
  rw [map_smul]
  change (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj V from
      (i.val.app V).hom b) •
    (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj V from
      ((SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf O')).val.map g).hom
      ((i.val.app U).hom a)) • G.val.map g x = 0
  rw [← mul_smul]
  have hab := hsq V b (Iₛ.val.map g a)
  change (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj V from
        (i.val.app V).hom b) *
      (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj V from
        (i.val.app V).hom (Iₛ.val.map g a)) = 0 at hab
  rw [hi] at hab
  rw [hab]
  simp

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
private lemma annihilatorQuotient_smul_eq_zero
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hsq : ∀ (U : Cᵒᵖ) (a b : I.val.obj U),
      (show O'.obj.obj U from i.val.app U a) *
        (show O'.obj.obj U from i.val.app U b) = 0)
    (U : Cᵒᵖ) (a : I.val.obj U) (x : G.val.obj U) :
    (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
      i.val.app U a) •
      Submodule.Quotient.mk
        (p := (annihilatorPresheafSubmodule f I i G).obj U) x = 0 := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact multiplication_mem_annihilatorPresheaf f I i G hsq U a x

private noncomputable def annihilatorSheaf
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O') :=
  (PresheafOfModules.sheafification
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).obj
    (annihilatorPresheafSubmodule f I i G).toPresheafOfModules

private noncomputable def annihilatorSheafInclusion
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')) :
    annihilatorSheaf f I i G ⟶ G := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf O'
  let N := annihilatorPresheafSubmodule f I i G
  let sh := PresheafOfModules.sheafification (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  exact (sh.map N.ι) ≫ adj.counit.app G

private lemma annihilatorSheafInclusion_mono
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')) :
    Mono (annihilatorSheafInclusion f I i G) := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf O'
  let N := annihilatorPresheafSubmodule f I i G
  let sh := PresheafOfModules.sheafification (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  have hsh : Mono (sh.map N.ι) := by
    apply (SheafOfModules.toSheaf R).mono_of_mono_map
    let φ := (presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf R.obj).map N.ι)
    have hlocal : Sheaf.IsLocallyInjective φ := by
      rw [Presheaf.isLocallyInjective_presheafToSheaf_map_iff]
      apply Presheaf.isLocallyInjective_of_injective
      intro U x y hxy
      exact Subtype.ext hxy
    exact Sheaf.mono_of_isLocallyInjective φ
  have hc : IsIso (adj.counit.app G) := by infer_instance
  have hcmono : Mono (adj.counit.app G) := inferInstance
  change Mono ((sh.map N.ι) ≫ adj.counit.app G)
  exact mono_comp' hsh hcmono

private noncomputable def annihilatorPresheafMap
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    {G H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')}
    (α : G ⟶ H) :
    (annihilatorPresheafSubmodule f I i G).toPresheafOfModules ⟶
      (annihilatorPresheafSubmodule f I i H).toPresheafOfModules := by
  let NG := annihilatorPresheafSubmodule f I i G
  let NH := annihilatorPresheafSubmodule f I i H
  refine { app := fun U => ModuleCat.ofHom ((α.val.app U).hom.comp
      (NG.obj U).subtype |>.codRestrict (NH.obj U) ?_), naturality := ?_ }
  · intro x V g a
    let c : (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj V :=
      i.val.app V a
    have hx : c • G.val.map g x.val = 0 := x.property V g a
    have h1 : c • H.val.map g (α.val.app U x.val)
        = c • α.val.app V (G.val.map g x.val) :=
      congrArg (fun t : H.val.obj V => c • t)
        (PresheafOfModules.naturality_apply α.val g x.val).symm
    have h2 : c • α.val.app V (G.val.map g x.val)
        = α.val.app V (c • G.val.map g x.val) :=
      ((α.val.app V).hom.map_smul c (G.val.map g x.val)).symm
    have h3 : α.val.app V (c • G.val.map g x.val) = 0 :=
      (congrArg (fun t : G.val.obj V => α.val.app V t) hx).trans (map_zero _)
    change c • H.val.map g (α.val.app U x.val) = 0
    exact h1.trans (h2.trans h3)
  · intro U V g
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    exact congrArg (fun h : ModuleCat.Hom _ _ => h.hom x.val) (α.val.naturality g)
omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
private lemma annihilatorPresheafMap_comp_inclusion
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    {G H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')}
    (α : G ⟶ H) :
    annihilatorPresheafMap f I i α ≫
        (annihilatorPresheafSubmodule f I i H).ι =
      (annihilatorPresheafSubmodule f I i G).ι ≫ α.val := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext x
  rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
private lemma annihilatorPresheaf_isPullback
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    {G H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')}
    (α : G ⟶ H) [Mono α] :
    IsPullback (annihilatorPresheafMap f I i α)
      (annihilatorPresheafSubmodule f I i G).ι
      (annihilatorPresheafSubmodule f I i H).ι α.val := by
  let NG := annihilatorPresheafSubmodule f I i G
  let NH := annihilatorPresheafSubmodule f I i H
  have : Mono α.val := mono_val_of_mono α
  apply IsPullback.mk' (annihilatorPresheafMap_comp_inclusion f I i α)
  · intro W x y _ hy
    exact (cancel_mono NG.ι).mp hy
  · intro W x y h
    let z : W ⟶ NG.toPresheafOfModules := {
      app := fun U => ModuleCat.ofHom
        ((y.app U).hom.codRestrict (NG.obj U) (by
          intro t V g a
          apply PresheafOfModules.injective_of_mono α.val V
          have ht := congrArg (fun k : W ⟶ H.val => (k.app V).hom (W.map g t)) h
          have hnat := (PresheafOfModules.naturality_apply y g t).symm
          change (x.app V (W.map g t)).val =
            α.val.app V (y.app V (W.map g t)) at ht
          change G.val.map g (y.app U t) = y.app V (W.map g t) at hnat
          have hxnat := (PresheafOfModules.naturality_apply x g t).symm
          have hv := congrArg Subtype.val hxnat
          change H.val.map g (x.app U t).val =
            (x.app V (W.map g t)).val at hv
          let : Module (O'.obj.obj V) (G.val.obj V) := (G.val.obj V).isModule
          let : Module (O'.obj.obj V) (H.val.obj V) := (H.val.obj V).isModule
          let r : O'.obj.obj V := i.val.app V a
          let z : G.val.obj V := G.val.map g (y.app U t)
          change (α.val.app V).hom
            (r • z) =
            (α.val.app V).hom 0
          have hlin := (α.val.app V).hom.map_smul r z
          refine hlin.trans ?_
          dsimp [z]
          rw [hnat, ← ht, ← hv]
          let hterm : H.val.obj V := H.val.map g (x.app U t).val
          have hzero : r • hterm = 0 :=
            (x.app U t).property V g a
          change r • hterm = (α.val.app V).hom 0
          rw [hzero, map_zero]))
      naturality := by
        intro U V g
        apply ModuleCat.hom_ext
        ext t
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply y g t }
    refine ⟨z, ?_, ?_⟩
    · apply (cancel_mono NH.ι).mp
      rw [Category.assoc, annihilatorPresheafMap_comp_inclusion, ← Category.assoc,
        show z ≫ NG.ι = y from by
          apply PresheafOfModules.hom_ext
          intro U
          apply ModuleCat.hom_ext
          ext t
          rfl]
      exact h.symm
    · apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.hom_ext
      ext t
      rfl

private noncomputable def annihilatorSheafMap
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    {G H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')}
    (α : G ⟶ H) :
    annihilatorSheaf f I i G ⟶ annihilatorSheaf f I i H :=
  (PresheafOfModules.sheafification
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).map
    (annihilatorPresheafMap f I i α)

private lemma annihilatorSheafMap_comp_inclusion
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    {G H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')}
    (α : G ⟶ H) :
    annihilatorSheafMap f I i α ≫ annihilatorSheafInclusion f I i H =
      annihilatorSheafInclusion f I i G ≫ α := by
  let sh := PresheafOfModules.sheafification
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)
  let ε := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).counit
  let NG := annihilatorPresheafSubmodule f I i G
  let NH := annihilatorPresheafSubmodule f I i H
  let a := annihilatorPresheafMap f I i α
  have hε : sh.map α.val ≫ ε.app H = ε.app G ≫ α := ε.naturality α
  have e1 : sh.map a ≫ sh.map NH.ι = sh.map NG.ι ≫ sh.map α.val := by
    rw [← Functor.map_comp, ← Functor.map_comp, annihilatorPresheafMap_comp_inclusion]
  change sh.map a ≫ (sh.map NH.ι ≫ ε.app H) =
    (sh.map NG.ι ≫ ε.app G) ≫ α
  calc
    sh.map a ≫ (sh.map NH.ι ≫ ε.app H) =
        (sh.map a ≫ sh.map NH.ι) ≫ ε.app H := (Category.assoc _ _ _).symm
    _ = (sh.map NG.ι ≫ sh.map α.val) ≫ ε.app H := e1 =≫ ε.app H
    _ = sh.map NG.ι ≫ (sh.map α.val ≫ ε.app H) := Category.assoc _ _ _
    _ = sh.map NG.ι ≫ (ε.app G ≫ α) := sh.map NG.ι ≫= hε
    _ = (sh.map NG.ι ≫ ε.app G) ≫ α := (Category.assoc _ _ _).symm
private lemma annihilatorSheafMap_mono
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    {G H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')}
    (α : G ⟶ H) [Mono α] :
    Mono (annihilatorSheafMap f I i α) := by
  have : Mono (annihilatorSheafInclusion f I i G) :=
    annihilatorSheafInclusion_mono f I i G
  exact mono_of_mono_fac (annihilatorSheafMap_comp_inclusion f I i α)

private lemma annihilatorSheaf_isPullback
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    {G H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')}
    (α : G ⟶ H) [Mono α] :
    IsPullback (annihilatorSheafMap f I i α)
      (annihilatorSheafInclusion f I i G)
      (annihilatorSheafInclusion f I i H) α := by
  let sh := PresheafOfModules.sheafification
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)
  let ε := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).counit
  have hnat : sh.map α.val ≫ ε.app H = ε.app G ≫ α := ε.naturality α
  have : HasSheafify J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have : IsIso ε := inferInstance
  let εG : sh.obj G.val ⟶ G := ε.app G
  let εH : sh.obj H.val ⟶ H := ε.app H
  have : IsIso εG := inferInstanceAs (IsIso (ε.app G))
  have : IsIso εH := inferInstanceAs (IsIso (ε.app H))
  have hnat' : sh.map α.val ≫ εH = εG ≫ α := hnat
  have hpb := (annihilatorPresheaf_isPullback f I i α).map sh
  have hiso : IsPullback (sh.map α.val) εG εH α := IsPullback.of_vert_isIso ⟨hnat'⟩
  exact hpb.paste_vert hiso
private lemma annihilatorCokernelMap_mono
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    {G H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')}
    (α : G ⟶ H) [Mono α] :
    Mono (cokernel.map (annihilatorSheafInclusion f I i G)
      (annihilatorSheafInclusion f I i H)
      (annihilatorSheafMap f I i α) α
      (annihilatorSheafMap_comp_inclusion f I i α).symm) :=
  Abelian.mono_cokernel_map_of_isPullback (annihilatorSheaf_isPullback f I i α).flip

private noncomputable def multiplicationPresheafMap_to_annihilator
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hsq : ∀ (U : Cᵒᵖ) (a b : I.val.obj U),
      (show O'.obj.obj U from i.val.app U a) *
        (show O'.obj.obj U from i.val.app U b) = 0) :
    MonoidalCategoryStruct.tensorObj
        ((SheafOfModules.restrictScalars (ringMap f)).obj I).val G.val ⟶
      (annihilatorPresheafSubmodule f I i G).toPresheafOfModules := by
  let N := annihilatorPresheafSubmodule f I i G
  let m := multiplicationPresheafMap f I G i
  refine {
    app := fun U => by
      letI : CommSemiring
          ((Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U) :=
        inferInstanceAs (CommSemiring (O'.obj.obj U))
      letI : Module
          ((Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U)
          (N.obj U) :=
        SMulMemClass.toModule (N.obj U)
      letI : CommSemiring ((O'.obj ⋙ forget₂ CommRingCat RingCat).obj U) :=
        inferInstanceAs (CommSemiring (O'.obj.obj U))
      letI : Module ((O'.obj ⋙ forget₂ CommRingCat RingCat).obj U) (N.obj U) :=
        SMulMemClass.toModule (N.obj U)
      letI : Module (O'.obj.obj U) (N.obj U) :=
        inferInstanceAs (Module ((O'.obj ⋙ forget₂ CommRingCat RingCat).obj U) (N.obj U))
      refine ModuleCat.ofHom ((m.app U).hom.codRestrict (N.obj U) ?_)
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a x => exact multiplication_mem_annihilatorPresheaf f I i G hsq U a x
      | add z₁ z₂ hz₁ hz₂ =>
          have ha : (m.app U).hom (z₁ + z₂) =
              (m.app U).hom z₁ + (m.app U).hom z₂ := map_add _ _ _
          exact Eq.mpr (congrArg (fun y : G.val.obj U => y ∈ N.obj U) ha)
            ((N.obj U).add_mem hz₁ hz₂)
    naturality := ?_ }
  · intro U V g
    apply ModuleCat.hom_ext
    ext z
    apply Subtype.ext
    exact congrArg (fun k : ModuleCat.Hom _ _ => k.hom z) (m.naturality g)
omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
private lemma multiplicationPresheafMap_to_annihilator_comp
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hsq : ∀ (U : Cᵒᵖ) (a b : I.val.obj U),
      (show O'.obj.obj U from i.val.app U a) *
        (show O'.obj.obj U from i.val.app U b) = 0) :
    multiplicationPresheafMap_to_annihilator f I i G hsq ≫
        (annihilatorPresheafSubmodule f I i G).ι =
      multiplicationPresheafMap f I G i := by
  let m := multiplicationPresheafMap f I G i
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext z
  change (m.app U).hom z = _
  rfl

private lemma multiplicationMap_factors_annihilator
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hsq : ∀ (U : Cᵒᵖ) (a b : I.val.obj U),
      (show O'.obj.obj U from i.val.app U a) *
        (show O'.obj.obj U from i.val.app U b) = 0) :
    multiplicationMap f I G i =
      (PresheafOfModules.sheafification
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).map
          (multiplicationPresheafMap_to_annihilator f I i G hsq) ≫
        annihilatorSheafInclusion f I i G := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf O'
  let sh := PresheafOfModules.sheafification (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let P := MonoidalCategoryStruct.tensorObj
    ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O')).obj
      ((SheafOfModules.restrictScalars (ringMap f)).obj I))
    ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O')).obj G)
  let N := annihilatorPresheafSubmodule f I i G
  let e := PresheafOfModules.sheafificationHomEquiv
    (α := 𝟙 R.obj) (P := P) (F := G)
  have he : e = adj.homEquiv P G :=
    sheafificationHomEquiv_eq_homEquiv _ _ _
  let t := multiplicationPresheafMap_to_annihilator f I i G hsq ≫ N.ι
  let ν := (sh.map (multiplicationPresheafMap_to_annihilator f I i G hsq)) ≫
    annihilatorSheafInclusion f I i G
  have hrhs :
      ν = (adj.homEquiv P G).symm t := by
    dsimp [annihilatorSheafInclusion]
    have h1 : (adj.homEquiv P G).symm
          (multiplicationPresheafMap_to_annihilator f I i G hsq ≫ N.ι) =
        sh.map (multiplicationPresheafMap_to_annihilator f I i G hsq ≫ N.ι) ≫
          adj.counit.app G := adj.homEquiv_counit P G _
    have h2 : sh.map (multiplicationPresheafMap_to_annihilator f I i G hsq ≫ N.ι) ≫
          adj.counit.app G =
        sh.map (multiplicationPresheafMap_to_annihilator f I i G hsq) ≫
          sh.map N.ι ≫ adj.counit.app G :=
      sh.map_comp_assoc _ _ _
    exact (h1.trans h2).symm
  have hν : ν = e.symm t := by rwa [he]
  apply (multiplicationMap_eq_of_tmul f I G i ν ?_).symm
  intro U a x
  rw [hν]
  have hlift := sheafificationLiftUnitApply (𝟙 R.obj) P G t U
    (a ⊗ₜ[O'.obj.obj U] x)
  have hcomp := congrArg (fun k => k.app U)
    (multiplicationPresheafMap_to_annihilator_comp f I i G hsq)
  calc
    (e.symm t).val.app U
        (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
            Stacks.SheafOfModules.Tensor.ringSheaf
            O')
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
      (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars (ringMap f)).obj I).val
          G.val)).app U
            (a ⊗ₜ[O'.obj.obj U] x)) = t.app U (a ⊗ₜ[O'.obj.obj U] x) := hlift
    _ = (multiplicationPresheafMap f I G i).app U
        (a ⊗ₜ[O'.obj.obj U] x) :=
      congrArg (fun morphism => morphism.hom (a ⊗ₜ[O'.obj.obj U] x)) hcomp
    _ = (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
        i.val.app U a) • x := rfl

/-- The morphism `I ⊗[O'] G ⟶ I ⊗[O'] H` induced by `α : G ⟶ H` on the second factor. -/
noncomputable def tensorSecondSheafMap
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    {I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {G H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')}
    (α : G ⟶ H) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj G)).obj
        ((SheafOfModules.restrictScalars (ringMap f)).obj I) ⟶
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj H)).obj
        ((SheafOfModules.restrictScalars (ringMap f)).obj I) := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf O'
  let sh := PresheafOfModules.sheafification (𝟙 R.obj)
  exact sh.map (MonoidalCategory.whiskerLeft
    ((SheafOfModules.restrictScalars (ringMap f)).obj I).val α.val)

/-- The multiplication maps are natural: `multiplicationMap f I G i ≫ α` equals
`tensorSecondSheafMap f α ≫ multiplicationMap f I H i`. -/
lemma multiplicationMap_natural
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {G H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')}
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (α : G ⟶ H) :
    multiplicationMap f I G i ≫ α =
      tensorSecondSheafMap f α ≫ multiplicationMap f I H i := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf O'
  let sh := PresheafOfModules.sheafification (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let PG := MonoidalCategoryStruct.tensorObj
    ((SheafOfModules.forget R).obj ((SheafOfModules.restrictScalars (ringMap f)).obj I))
    ((SheafOfModules.forget R).obj G)
  let PH := MonoidalCategoryStruct.tensorObj
    ((SheafOfModules.forget R).obj ((SheafOfModules.restrictScalars (ringMap f)).obj I))
    ((SheafOfModules.forget R).obj H)
  apply (adj.homEquiv PG H).injective
  have hG : adj.homEquiv PG G (multiplicationMap f I G i) =
      multiplicationPresheafMap f I G i :=
    (PresheafOfModules.sheafificationAdjunction_homEquiv_apply
      (𝟙 R.obj) (multiplicationMap f I G i)).trans
        ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).apply_symm_apply _)
  have hH : adj.homEquiv PH H (multiplicationMap f I H i) =
      multiplicationPresheafMap f I H i :=
    (PresheafOfModules.sheafificationAdjunction_homEquiv_apply
      (𝟙 R.obj) (multiplicationMap f I H i)).trans
        ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).apply_symm_apply _)
  have hL : adj.homEquiv PG H (multiplicationMap f I G i ≫ α) =
      multiplicationPresheafMap f I G i ≫ α.val := by
    refine (adj.homEquiv_naturality_right _ _).trans ?_
    change adj.homEquiv PG G (multiplicationMap f I G i) ≫ α.val = _
    rw [hG]
    rfl
  have hR : adj.homEquiv PG H (tensorSecondSheafMap f α ≫ multiplicationMap f I H i) =
      MonoidalCategory.whiskerLeft
          ((SheafOfModules.restrictScalars (ringMap f)).obj I).val α.val ≫
        multiplicationPresheafMap f I H i := by
    refine (adj.homEquiv_naturality_left (MonoidalCategory.whiskerLeft
      ((SheafOfModules.restrictScalars (ringMap f)).obj I).val α.val)
      (multiplicationMap f I H i)).trans ?_
    change MonoidalCategory.whiskerLeft
        ((SheafOfModules.restrictScalars (ringMap f)).obj I).val α.val ≫
      adj.homEquiv PH H (multiplicationMap f I H i) = _
    rw [hH]
    rfl
  exact (hL.trans (multiplicationPresheafMap_natural f I i α)).trans hR.symm
private lemma reduction_kernel_map_mono
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (S : ShortComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')))
    (hS : S.ShortExact) (hmono : Mono (multiplicationMap f I S.X₃ i)) :
    Mono (cokernel.map (multiplicationMap f I S.X₁ i)
      (multiplicationMap f I S.X₂ i) (tensorSecondSheafMap f S.f) S.f
      (multiplicationMap_natural f I i S.f)) := by
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O')).obj
    ((SheafOfModules.restrictScalars (ringMap f)).obj I)
  have := tensorLeft_preservesColimits O' ((SheafOfModules.restrictScalars (ringMap f)).obj I)
  let φ : S.map T ⟶ S :=
    { τ₁ := multiplicationMap f I S.X₁ i
      τ₂ := multiplicationMap f I S.X₂ i
      τ₃ := multiplicationMap f I S.X₃ i
      comm₁₂ := multiplicationMap_natural f I i S.f
      comm₂₃ := multiplicationMap_natural f I i S.g }
  have : Mono S.f := hS.mono_f
  have : Mono φ.τ₃ := hmono
  exact mono_cokernelMap_of_exact_of_mono φ
    (hS.exact.map_of_epi_of_preservesCokernel T hS.epi_g inferInstance)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
private lemma isFlat_of_iso
    {O : Sheaf J CommRingCat.{w}}
    {F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (e : F ≅ G)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat F) :
    AlgebraicGeometry.SheafOfModules.IsFlat G :=
  (exactFunctor _ _).prop_of_iso
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.mapIso e) hF

private lemma multiplicationMap_eq_map_comp_counit
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O')) :
    multiplicationMap f I G i =
      (PresheafOfModules.sheafification
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).map
        (multiplicationPresheafMap f I G i) ≫
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).counit.app G := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)
  let P := MonoidalCategoryStruct.tensorObj
    ((SheafOfModules.restrictScalars (ringMap f)).obj I).val G.val
  have he : PresheafOfModules.sheafificationHomEquiv
      (α := 𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)
      (P := P) (F := G) =
      adj.homEquiv P G :=
    sheafificationHomEquiv_eq_homEquiv _ _ _
  unfold multiplicationMap
  exact (congrArg (fun q => q.symm (multiplicationPresheafMap f I G i)) he).trans
    (adj.homEquiv_counit P G (multiplicationPresheafMap f I G i))

/-- If `i` is a monomorphism and `G` is flat, then `multiplicationMap f I G i` is a
monomorphism. -/
lemma multiplicationMap_mono_of_flat
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    [Mono i] (hG : AlgebraicGeometry.SheafOfModules.IsFlat G) :
    Mono (multiplicationMap f I G i) := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf O'
  let sh := PresheafOfModules.sheafification (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  have heq : multiplicationPresheafMap f I G i =
      MonoidalCategory.whiskerRight i.val G.val ≫
        (MonoidalCategory.leftUnitor G.val).hom := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a x
    rfl
  have hm : Mono (sh.map (MonoidalCategory.whiskerRight i.val G.val)) :=
    flat_tensor_preserves_mono O' G hG i
  have hc : IsIso (adj.counit.app G) := inferInstance
  have hu : IsIso (sh.map (MonoidalCategory.leftUnitor G.val).hom) := inferInstance
  have h1 : sh.map (multiplicationPresheafMap f I G i) =
      sh.map (MonoidalCategory.whiskerRight i.val G.val ≫
        (MonoidalCategory.leftUnitor G.val).hom) :=
    congrArg (fun k => sh.map k) heq
  have h2 : sh.map (MonoidalCategory.whiskerRight i.val G.val ≫
        (MonoidalCategory.leftUnitor G.val).hom) =
      sh.map (MonoidalCategory.whiskerRight i.val G.val) ≫
        sh.map (MonoidalCategory.leftUnitor G.val).hom :=
    sh.map_comp _ _
  have hmap : multiplicationMap f I G i =
      (sh.map (MonoidalCategory.whiskerRight i.val G.val) ≫
        sh.map (MonoidalCategory.leftUnitor G.val).hom) ≫ adj.counit.app G :=
    (multiplicationMap_eq_map_comp_counit f I G i).trans
      (congrArg (fun k => k ≫ adj.counit.app G) (h1.trans h2))
  have hu' : Mono (sh.map (MonoidalCategory.leftUnitor G.val).hom) := inferInstance
  have hc' : Mono (adj.counit.app G) := inferInstance
  rw [hmap]
  exact mono_comp' (mono_comp' hm hu') hc'
private noncomputable def restrictScalarsFullyFaithful
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (hf : Presheaf.IsLocallySurjective J f.hom) :
    (SheafOfModules.restrictScalars.{w} (ringMap f)).FullyFaithful := by
  letI : Presheaf.IsLocallySurjective J (ringMap f).hom := ⟨hf.imageSieve_mem⟩
  exact
    { preimage := fun {M N} g =>
        ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
          (ringMap f).hom N.isSheaf).symm g.val⟩
      map_preimage := fun g => SheafOfModules.hom_ext
        ((PresheafOfModules.restrictHomEquivOfIsLocallySurjective
          (ringMap f).hom _).apply_symm_apply g.val)
      preimage_map := fun g => SheafOfModules.hom_ext
        ((PresheafOfModules.restrictHomEquivOfIsLocallySurjective
          (ringMap f).hom _).symm_apply_apply g.val) }

private lemma multiplicationMap_comp_restrictScalars
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hi_zero : ∀ (U : Cᵒᵖ) (a : I.val.obj U),
      f.hom.app U (show O'.obj.obj U from i.val.app U a) = 0)
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (g : G ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj N) :
    multiplicationMap f I G i ≫ g = 0 := by
  apply (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a x
  change g.val.app U ((multiplicationMap f I G i).val.app U
    (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
        Stacks.SheafOfModules.Tensor.ringSheaf O')
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
      (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars (ringMap f)).obj I).val
          G.val)).app U
        (a ⊗ₜ[O'.obj.obj U] x))) = 0
  have hmul : (multiplicationMap f I G i).val.app U
      (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf O')
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
      (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars (ringMap f)).obj I).val
          G.val)).app U
          (a ⊗ₜ[O'.obj.obj U] x)) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
        i.val.app U a) • x :=
    multiplicationMap_tmul f I G i U (show I.val.obj U from a) x
  refine (congrArg (g.val.app U).hom hmul).trans
    (((g.val.app U).hom.map_smul
      (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
        i.val.app U a) x).trans ?_)
  let : Module (O.obj.obj U) (N.val.obj U) := (N.val.obj U).isModule
  have hz : f.hom.app U
      (show O'.obj.obj U from i.val.app U (show I.val.obj U from a)) = 0 :=
    hi_zero U (show I.val.obj U from a)
  change @SMul.smul (O.obj.obj U) (N.val.obj U) inferInstance
    (f.hom.app U (show O'.obj.obj U from i.val.app U (show I.val.obj U from a)))
      (g.val.app U x) = 0
  exact (congrArg (fun scalar : O.obj.obj U =>
    scalar • (show N.val.obj U from g.val.app U x)) hz).trans
    (zero_smul _ _)
private noncomputable def reductionIsoChangeOfRings
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (hf : Presheaf.IsLocallySurjective J f.hom)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hi_zero : ∀ (U : Cᵒᵖ) (a : I.val.obj U),
      f.hom.app U (show O'.obj.obj U from i.val.app U a) = 0)
    (q : G ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj F)
    (hzero : multiplicationMap f I G i ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q hzero)) :
    F ≅ (Stacks.FlatChangeOfRings.extendScalars f).obj G := by
  let adj := Stacks.FlatChangeOfRings.extendScalarsAdjunction f
  let ff := restrictScalarsFullyFaithful f hf
  let eta := adj.unit.app G
  let hη := multiplicationMap_comp_restrictScalars f I G i hi_zero _ eta
  let a := (CokernelCofork.IsColimit.desc' hq eta hη)
  let b := (adj.homEquiv G F).symm q
  have ha : q ≫ a.1 = eta := a.2
  have hb : eta ≫ (SheafOfModules.restrictScalars (ringMap f)).map b = q :=
    (adj.homEquiv G F).apply_symm_apply q
  refine ⟨ff.preimage a.1, b, ?_, ?_⟩
  · apply ff.map_injective
    rw [(SheafOfModules.restrictScalars (ringMap f)).map_comp (ff.preimage a.1) b,
      ff.map_preimage a.1, (SheafOfModules.restrictScalars (ringMap f)).map_id F]
    apply Cofork.IsColimit.hom_ext hq
    change q ≫ (a.1 ≫ (SheafOfModules.restrictScalars (ringMap f)).map b) = q ≫ 𝟙 _
    exact (Category.assoc q a.1 ((SheafOfModules.restrictScalars (ringMap f)).map b)).symm.trans
      (((congrArg (fun morphism => morphism ≫
        (SheafOfModules.restrictScalars (ringMap f)).map b) ha).trans hb).trans
          (Category.comp_id q).symm)
  · apply (adj.homEquiv G _).injective
    change eta ≫ (SheafOfModules.restrictScalars (ringMap f)).map
      (b ≫ ff.preimage a.1) = eta ≫
      (SheafOfModules.restrictScalars (ringMap f)).map (𝟙 _)
    rw [(SheafOfModules.restrictScalars (ringMap f)).map_comp b (ff.preimage a.1),
      ff.map_preimage a.1,
      (SheafOfModules.restrictScalars (ringMap f)).map_id
        ((Stacks.FlatChangeOfRings.extendScalars f).obj G)]
    exact (Category.assoc eta ((SheafOfModules.restrictScalars (ringMap f)).map b) a.1).symm.trans
      ((congrArg (fun morphism => morphism ≫ a.1) hb).trans
        (ha.trans (Category.comp_id eta).symm))

/-- The morphism of presheaves of `O'`-modules `B ⊗[O'] G ⟶ B ⊗[O] F` sending `b ⊗ x` to
`b ⊗ q x`, the target being an `O'`-module by restriction of scalars. -/
noncomputable def reductionTensorPresheafMap
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (q : G ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj F) :
    MonoidalCategoryStruct.tensorObj
      ((SheafOfModules.restrictScalars (ringMap f)).obj B).val G.val ⟶
      (PresheafOfModules.restrictScalars (ringMap f).hom).obj
        (PresheafOfModules.tensorObj B.val F.val) where
  app U := by
    letI : Module (O.obj.obj U)
        (((SheafOfModules.restrictScalars (ringMap f)).obj B).val.obj U) :=
      (B.val.obj U).isModule
    letI : Module (O.obj.obj U)
        (((SheafOfModules.restrictScalars (ringMap f)).obj F).val.obj U) :=
      (F.val.obj U).isModule
    letI : Module (O.obj.obj U) (F.val.obj U) := (F.val.obj U).isModule
    exact ModuleCat.MonoidalCategory.tensorLift
      (fun b x => b ⊗ₜ[O.obj.obj U] (q.val.app U x : F.val.obj U))
      (by intro b b' x; exact TensorProduct.add_tmul _ _ _)
      (by
        intro r b x
        change ((f.hom.app U r) • b) ⊗ₜ[O.obj.obj U] (q.val.app U x : F.val.obj U) =
          (f.hom.app U r) • (b ⊗ₜ[O.obj.obj U] (q.val.app U x : F.val.obj U))
        exact TensorProduct.smul_tmul' _ _ _)
      (by intro b x y; rw [map_add]; exact TensorProduct.tmul_add _ _ _)
      (by
        intro r b x
        have h : (q.val.app U
              ((show (Stacks.SheafOfModules.Tensor.ringSheaf
                O').obj.obj U from r) • x) : F.val.obj U) =
            f.hom.app U r • (q.val.app U x : F.val.obj U) :=
          map_smul (ConcreteCategory.hom (q.val.app U)) _ x
        exact (congrArg (fun y : F.val.obj U => b ⊗ₜ[O.obj.obj U] y) h).trans
          (map_smul ((TensorProduct.mk (O.obj.obj U) _ (F.val.obj U)) b)
            (f.hom.app U r) (q.val.app U x : F.val.obj U)))
  naturality {U V} g := by
    let : Module (O.obj.obj V)
        (((SheafOfModules.restrictScalars (ringMap f)).obj B).val.obj V) :=
      (B.val.obj V).isModule
    let : Module (O.obj.obj V)
        (((SheafOfModules.restrictScalars (ringMap f)).obj F).val.obj V) :=
      (F.val.obj V).isModule
    let : Module (O.obj.obj V)
        ((ModuleCat.restrictScalars (RingCat.Hom.hom
          ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.map g))).obj
            (B.val.obj V)) := (B.val.obj V).isModule
    let : Module (O.obj.obj V)
        ((ModuleCat.restrictScalars (RingCat.Hom.hom
          ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.map g))).obj
            (F.val.obj V)) := (F.val.obj V).isModule
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro b x
    change B.val.map g b ⊗ₜ[O.obj.obj V] (q.val.app V (G.val.map g x) : F.val.obj V) =
      B.val.map g b ⊗ₜ[O.obj.obj V] F.val.map g (q.val.app U x)
    rw [PresheafOfModules.naturality_apply q.val]
    rfl

/-- The morphism of sheaves of `O'`-modules `B ⊗[O'] G ⟶ B ⊗[O] F` induced by
`q : G ⟶ F`, sending `b ⊗ x` to `b ⊗ q x`. -/
noncomputable def reductionTensorMap
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (q : G ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj F) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj G)).obj
      ((SheafOfModules.restrictScalars (ringMap f)).obj B) ⟶
      (SheafOfModules.restrictScalars (ringMap f)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F)).obj B) :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).symm
    (reductionTensorPresheafMap f B G F q ≫
      (PresheafOfModules.restrictScalars (ringMap f).hom).map
        ((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
            Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
      (PresheafOfModules.tensorObj B.val F.val)))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Tensoring `g : A ⟶ B` on the right with `F` sends the image of `a ⊗ x` to the image of
`g a ⊗ x`. -/
lemma tensorRight_map_tmul
    (O : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (g : A ⟶ B)
    (U : Cᵒᵖ) (a : A.val.obj U) (x : F.val.obj U) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F)).map g).val.app U
      (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
      (PresheafOfModules.tensorObj A.val F.val)).app U
        (a ⊗ₜ[O.obj.obj U] x)) =
      ((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
      (PresheafOfModules.tensorObj B.val F.val)).app U
        (g.val.app U a ⊗ₜ[O.obj.obj U] x) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
  exact congrArg (fun k => k.app U (a ⊗ₜ[O.obj.obj U] x))
    (adj.unit.naturality (MonoidalCategory.whiskerRight g.val F.val)).symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Tensoring `g : F ⟶ G` on the left with `A` sends the image of `a ⊗ x` to the image of
`a ⊗ g x`. -/
lemma tensorLeft_map_tmul
    (O : Sheaf J CommRingCat.{w})
    (A : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (g : F ⟶ G)
    (U : Cᵒᵖ) (a : A.val.obj U) (x : F.val.obj U) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj A).map g).val.app U
      (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
      (PresheafOfModules.tensorObj A.val F.val)).app U
        (a ⊗ₜ[O.obj.obj U] x)) =
      ((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
      (PresheafOfModules.tensorObj A.val G.val)).app U
        (a ⊗ₜ[O.obj.obj U] g.val.app U x) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
  exact congrArg (fun k => k.app U (a ⊗ₜ[O.obj.obj U] x))
    (adj.unit.naturality (MonoidalCategory.whiskerLeft A.val g.val)).symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Two morphisms out of a tensor product `A ⊗ B` of sheaves of `O`-modules are equal if they
agree on the images of all pure tensors. -/
lemma tensorSheaf_hom_ext
    (O : Sheaf J CommRingCat.{w})
    (A B H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {g h : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj A).obj B ⟶ H}
    (heq : ∀ (U : Cᵒᵖ) (a : A.val.obj U) (b : B.val.obj U),
      g.val.app U (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
      (PresheafOfModules.tensorObj A.val B.val)).app U
        (a ⊗ₜ[O.obj.obj U] b)) =
      h.val.app U (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
      (PresheafOfModules.tensorObj A.val B.val)).app U
        (a ⊗ₜ[O.obj.obj U] b))) : g = h := by
  apply (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  exact heq U

/-- `reductionTensorMap f B G F q` sends the image of `b ⊗ x` to the image of `b ⊗ q x`. -/
lemma reductionTensorMap_tmul
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (q : G ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj F)
    (U : Cᵒᵖ) (b : B.val.obj U) (x : G.val.obj U) :
    (reductionTensorMap f B G F q).val.app U
      (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf O')
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
      (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars (ringMap f)).obj B).val
          G.val)).app U
          (b ⊗ₜ[O'.obj.obj U] x)) =
      ((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
      (PresheafOfModules.tensorObj B.val F.val)).app U
        (b ⊗ₜ[O.obj.obj U] (q.val.app U x : F.val.obj U)) :=
  sheafificationLiftUnitApply
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj) _ _ _ _ _

/-- `reductionTensorMap` is natural in the first factor `B`. -/
lemma reductionTensorMap_natural_left
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    {A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (g : A ⟶ B)
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (q : G ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj F) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj G)).map
        ((SheafOfModules.restrictScalars (ringMap f)).map g) ≫
        reductionTensorMap f B G F q =
      reductionTensorMap f A G F q ≫
        (SheafOfModules.restrictScalars (ringMap f)).map
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F)).map g) := by
  apply tensorSheaf_hom_ext O' ((SheafOfModules.restrictScalars (ringMap f)).obj A) G
  intro U a x
  have h4 := tensorRight_map_tmul O' G
    ((SheafOfModules.restrictScalars (ringMap f)).map g) U a x
  have h1 := reductionTensorMap_tmul f B G F q U
    (((SheafOfModules.restrictScalars (ringMap f)).map g).val.app U a) x
  have h3 := reductionTensorMap_tmul f A G F q U a x
  have h2 := tensorRight_map_tmul O F g U (a : A.val.obj U)
    (q.val.app U x : F.val.obj U)
  change (reductionTensorMap f B G F q).val.app U
      (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj G)).map
        ((SheafOfModules.restrictScalars (ringMap f)).map g)).val.app U _) =
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F)).map g).val.app U
      ((reductionTensorMap f A G F q).val.app U _)
  exact (congrArg (fun z => (reductionTensorMap f B G F q).val.app U z) h4).trans
    (h1.trans (h2.symm.trans (congrArg (fun z =>
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F)).map g).val.app
        U z) h3).symm))

/-- `reductionTensorMap` is natural with respect to a commutative square
`q ≫ k = g ≫ r`. -/
lemma reductionTensorMap_natural_right
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {G H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')}
    {F K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (q : G ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj F)
    (r : H ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj K)
    (g : G ⟶ H) (k : F ⟶ K)
    (comm : q ≫ (SheafOfModules.restrictScalars (ringMap f)).map k = g ≫ r) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O')).obj
        ((SheafOfModules.restrictScalars (ringMap f)).obj B)).map g ≫
        reductionTensorMap f B H K r =
      reductionTensorMap f B G F q ≫
        (SheafOfModules.restrictScalars (ringMap f)).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj B).map k) := by
  apply tensorSheaf_hom_ext O' ((SheafOfModules.restrictScalars (ringMap f)).obj B) G
  intro U b x
  have hA := tensorLeft_map_tmul O' ((SheafOfModules.restrictScalars (ringMap f)).obj B) g U b x
  have hB := reductionTensorMap_tmul f B H K r U b (g.val.app U x)
  have hC := reductionTensorMap_tmul f B G F q U b x
  have hD := tensorLeft_map_tmul O B k U b (q.val.app U x)
  have h := congrArg (fun t => t.val.app U x) comm
  change k.val.app U (q.val.app U x) = r.val.app U (g.val.app U x) at h
  change (reductionTensorMap f B H K r).val.app U
      ((((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O')).obj
        ((SheafOfModules.restrictScalars (ringMap f)).obj B)).map g).val.app U _) =
    (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj B).map k).val.app U
      ((reductionTensorMap f B G F q).val.app U _)
  exact (congrArg (fun z => (reductionTensorMap f B H K r).val.app U z) hA).trans
    (hB.trans ((congrArg (fun y : K.val.obj U =>
        ((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
            Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
      (PresheafOfModules.tensorObj B.val K.val)).app U
          (b ⊗ₜ[O.obj.obj U] y)) h.symm).trans
      (hD.symm.trans (congrArg (fun z =>
        (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj B).map k).val.app U z)
          hC).symm)))
private lemma reductionTensorPresheafMap_locallySurjective
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (q : G ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj F) [Epi q] :
    PresheafOfModules.IsLocallySurjective J (reductionTensorPresheafMap f B G F q) := by
  have : HasSheafify J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let qp := (PresheafOfModules.toPresheaf
    (Stacks.SheafOfModules.Tensor.ringSheaf O').obj).map q.val
  have : Presheaf.IsLocallySurjective J qp := by
    change Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf _).map q)
    exact (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{w} _).mpr inferInstance
  let t := (PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf O').obj).map
    (reductionTensorPresheafMap f B G F q)
  constructor
  intro U z
  change Presheaf.imageSieve t z ∈ J U
  let : Module (O.obj.obj (Opposite.op U)) (B.val.obj (Opposite.op U)) :=
    (B.val.obj (Opposite.op U)).isModule
  let : Module (O.obj.obj (Opposite.op U)) (F.val.obj (Opposite.op U)) :=
    (F.val.obj (Opposite.op U)).isModule
  change B.val.obj (Opposite.op U) ⊗[O.obj.obj (Opposite.op U)] F.val.obj (Opposite.op U) at z
  induction z using TensorProduct.inductionOn with
  | tmul b x =>
    apply J.superset_covering (S := Presheaf.imageSieve qp x) _
      (Presheaf.imageSieve_mem J qp x)
    rintro V g ⟨y, hy⟩
    let : Module (O.obj.obj (Opposite.op V))
        (((SheafOfModules.restrictScalars (ringMap f)).obj F).val.obj (Opposite.op V)) :=
      (F.val.obj (Opposite.op V)).isModule
    let : Module (O.obj.obj (Opposite.op V)) (F.val.obj (Opposite.op V)) :=
      (F.val.obj (Opposite.op V)).isModule
    let : Module (O.obj.obj (Opposite.op V))
        ((ModuleCat.restrictScalars (RingCat.Hom.hom
          ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.map g.op))).obj
            (B.val.obj (Opposite.op V))) := (B.val.obj (Opposite.op V)).isModule
    let : Module (O.obj.obj (Opposite.op V))
        ((ModuleCat.restrictScalars (RingCat.Hom.hom
          ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.map g.op))).obj
            (F.val.obj (Opposite.op V))) := (F.val.obj (Opposite.op V)).isModule
    refine ⟨B.val.map g.op b ⊗ₜ[O'.obj.obj (Opposite.op V)] y, ?_⟩
    change B.val.map g.op b ⊗ₜ[O.obj.obj (Opposite.op V)]
      (q.val.app (Opposite.op V) y : F.val.obj (Opposite.op V)) =
      B.val.map g.op b ⊗ₜ[O.obj.obj (Opposite.op V)] F.val.map g.op x
    exact congrArg (fun y : F.val.obj (Opposite.op V) =>
      B.val.map g.op b ⊗ₜ[O.obj.obj (Opposite.op V)] y) hy
  | add z z' hz hz' =>
    apply J.superset_covering (S := Presheaf.imageSieve t z ⊓ Presheaf.imageSieve t z') _
      (J.intersection_covering hz hz')
    rintro V g ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩
    refine ⟨y + y', ?_⟩
    simp only [map_add, hy, hy']
    exact (map_add _ z z').symm

/-- If `q` is an epimorphism, then so is `reductionTensorMap f B G F q`. -/
lemma reductionTensorMap_epi
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (q : G ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj F) [Epi q] :
    Epi (reductionTensorMap f B G F q) := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf O'
  let toP := PresheafOfModules.toPresheaf R.obj
  let p := reductionTensorPresheafMap f B G F q
  let u := (PresheafOfModules.restrictScalars (ringMap f).hom).map
    ((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
        Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
      (PresheafOfModules.tensorObj B.val F.val))
  have hp : Presheaf.IsLocallySurjective J (toP.map p) :=
    reductionTensorPresheafMap_locallySurjective f B G F q
  have hu : Presheaf.IsLocallySurjective J (toP.map u) := by
    change Presheaf.IsLocallySurjective J
      (toSheafify J (PresheafOfModules.tensorObj B.val F.val).presheaf)
    infer_instance
  have hpu := @Presheaf.isLocallySurjective_comp _ _ J _ _ _ _ _ _ _ _ _
    (toP.map p) (toP.map u) hp hu
  have ht : Presheaf.IsLocallySurjective J
      (toP.map (reductionTensorMap f B G F q).val) := by
    have heq :
        (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app _ ≫
          (reductionTensorMap f B G F q).val = p ≫ u :=
      (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)
        (F := (SheafOfModules.restrictScalars (ringMap f)).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F)).obj
            B))).apply_symm_apply (p ≫ u)
    have heq' := (CategoryTheory.Functor.map_comp toP _ _).symm.trans
      ((congrArg toP.map heq).trans (CategoryTheory.Functor.map_comp toP p u))
    exact @Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ _ J _ _ _ _ _ _ _ _ _
      _ _ _ heq' hpu
  apply (SheafOfModules.toSheaf.{w} R).epi_of_epi_map
  have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map
      (reductionTensorMap f B G F q)) := ht
  exact Sheaf.epi_of_isLocallySurjective _
private lemma multiplicationMap_comp_annihilatorCokernel
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hsq : ∀ (U : Cᵒᵖ) (a b : I.val.obj U),
      (show O'.obj.obj U from i.val.app U a) *
        (show O'.obj.obj U from i.val.app U b) = 0) :
    multiplicationMap f I G i ≫ cokernel.π (annihilatorSheafInclusion f I i G) = 0 := by
  have key : annihilatorSheafInclusion f I i G ≫
      cokernel.π (annihilatorSheafInclusion f I i G) = 0 :=
    cokernel.condition _
  refine Eq.trans (congrArg
    (fun k => k ≫ cokernel.π (annihilatorSheafInclusion f I i G))
    (multiplicationMap_factors_annihilator f I i G hsq)) ?_
  exact (Category.assoc _ _ _).trans
    ((congrArg (CategoryStruct.comp _) key).trans Limits.comp_zero)

/-- The multiplication map into the cokernel of `annihilatorSheafInclusion` vanishes. -/
private lemma multiplicationMap_annihilatorCokernel_eq_zero
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hsq : ∀ (U : Cᵒᵖ) (a b : I.val.obj U),
      (show O'.obj.obj U from i.val.app U a) *
        (show O'.obj.obj U from i.val.app U b) = 0) :
    multiplicationMap f I (cokernel (annihilatorSheafInclusion f I i G)) i = 0 := by
  let g := cokernel.π (annihilatorSheafInclusion f I i G)
  have hg : Epi g := inferInstance
  have ht : Epi (tensorSecondSheafMap f (I := I) g) :=
    epi_tensorLeft_map O' ((SheafOfModules.restrictScalars (ringMap f)).obj I) g
  apply (cancel_epi (tensorSecondSheafMap f (I := I) g)).mp
  rw [← multiplicationMap_natural f I i g]
  exact multiplicationMap_comp_annihilatorCokernel f I i G hsq

private lemma multiplicationMap_cokernel_eq_zero
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')) :
    multiplicationMap f I (cokernel (multiplicationMap f I G i)) i = 0 := by
  let ν := multiplicationMap f I G i
  let q := cokernel.π ν
  have ht : Epi (tensorSecondSheafMap f (I := I) q) :=
    epi_tensorLeft_map O' ((SheafOfModules.restrictScalars (ringMap f)).obj I) q
  apply (cancel_epi (tensorSecondSheafMap f (I := I) q)).mp
  rw [← multiplicationMap_natural f I i q]
  exact cokernel.condition ν

private lemma smul_eq_zero_of_multiplicationMap_eq_zero
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hi_univ : ∀ (U : Cᵒᵖ) (x : O'.obj.obj U), f.hom.app U x = 0 →
      ∃! a : I.val.obj U, (show O'.obj.obj U from i.val.app U a) = x)
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hzero : multiplicationMap f I G i = 0)
    (U : Cᵒᵖ) (r : (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U)
    (hr : (ringMap f).hom.app U r = 0) (x : G.val.obj U) : r • x = 0 := by
  obtain ⟨a, ha, _⟩ := hi_univ U r hr
  let z := ((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
      Stacks.SheafOfModules.Tensor.ringSheaf
      O')
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
      (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars (ringMap f)).obj I).val
          G.val)).app U
      (a ⊗ₜ[O'.obj.obj U] x)
  have h := congrArg (fun k :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj G)).obj
      ((SheafOfModules.restrictScalars (ringMap f)).obj I) ⟶ G =>
      k.val.app U z) hzero
  rw [multiplicationMap_tmul] at h
  have h' : (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
      i.val.app U a) • x = 0 := h
  have ha' : (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
      i.val.app U a) = r := ha
  exact ha' ▸ h'
private noncomputable def multiplicationCokernelDescend
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (hf : Presheaf.IsLocallySurjective J f.hom)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hi_univ : ∀ (U : Cᵒᵖ) (x : O'.obj.obj U), f.hom.app U x = 0 →
      ∃! a : I.val.obj U, (show O'.obj.obj U from i.val.app U a) = x)
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')) :
    Σ N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O),
      (SheafOfModules.restrictScalars (ringMap f)).obj N ≅
        cokernel (multiplicationMap f I G i) := by
  letI : Presheaf.IsLocallySurjective J (ringMap f).hom := ⟨hf.imageSieve_mem⟩
  apply descendModule (ringMap f) _
  intro U r hr x
  exact smul_eq_zero_of_multiplicationMap_eq_zero f I i hi_univ _
    (multiplicationMap_cokernel_eq_zero f I i G) U r hr x

private noncomputable def annihilatorCokernelDescend
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (hf : Presheaf.IsLocallySurjective J f.hom)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hi_univ : ∀ (U : Cᵒᵖ) (x : O'.obj.obj U), f.hom.app U x = 0 →
      ∃! a : I.val.obj U, (show O'.obj.obj U from i.val.app U a) = x)
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hsq : ∀ (U : Cᵒᵖ) (a b : I.val.obj U),
      (show O'.obj.obj U from i.val.app U a) *
        (show O'.obj.obj U from i.val.app U b) = 0) :
    Σ N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O),
      (SheafOfModules.restrictScalars (ringMap f)).obj N ≅
        cokernel (annihilatorSheafInclusion f I i G) := by
  letI : Presheaf.IsLocallySurjective J (ringMap f).hom := ⟨hf.imageSieve_mem⟩
  apply descendModule (ringMap f) _
  intro U r hr x
  exact smul_eq_zero_of_multiplicationMap_eq_zero f I i hi_univ _
    (multiplicationMap_annihilatorCokernel_eq_zero f I i G hsq) U r hr x

private lemma annihilatorSheafInclusion_smul_zero
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (U : Cᵒᵖ) (a : I.val.obj U) (x : (annihilatorSheaf f I i G).val.obj U) :
    (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
        i.val.app U a) •
      (annihilatorSheafInclusion f I i G).val.app U x = 0 := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf O'
  let N := annihilatorPresheafSubmodule f I i G
  let A := annihilatorSheaf f I i G
  let sh := PresheafOfModules.sheafification (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let η := adj.unit.app N.toPresheafOfModules
  let p := (PresheafOfModules.toPresheaf R.obj).map η
  have hp : Presheaf.IsLocallySurjective J p := by
    change Presheaf.IsLocallySurjective J (toSheafify J N.toPresheafOfModules.presheaf)
    infer_instance
  have he : PresheafOfModules.sheafificationHomEquiv
      (α := 𝟙 R.obj) (P := N.toPresheafOfModules) (F := G) =
      adj.homEquiv N.toPresheafOfModules G :=
    sheafificationHomEquiv_eq_homEquiv _ _ _
  have hinc : annihilatorSheafInclusion f I i G =
      (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm N.ι := by
    rw [he]
    dsimp [annihilatorSheafInclusion]
    exact (adj.homEquiv_counit N.toPresheafOfModules G N.ι).symm
  have hunit (V : Cᵒᵖ) (y : N.toPresheafOfModules.obj V) :
      (annihilatorSheafInclusion f I i G).val.app V (η.app V y) = y.val := by
    rw [hinc]
    exact sheafificationLiftUnitApply (𝟙 R.obj) N.toPresheafOfModules G N.ι V y
  let c : (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U :=
    i.val.app U a
  change c • (annihilatorSheafInclusion f I i G).val.app U x = 0
  apply G.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J p x)
  rintro V g ⟨y, hy⟩
  change G.val.map g.op
    (c • (annihilatorSheafInclusion f I i G).val.app U x) =
      G.val.map g.op 0
  rw [G.val.map_smul, map_zero]
  let Iₛ := (SheafOfModules.restrictScalars (ringMap f)).obj I
  let aₛ : Iₛ.val.obj U := a
  have hnat : (i.val.app (Opposite.op V)).hom (Iₛ.val.map g.op a) =
      ((SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf O')).val.map g.op).hom
        ((i.val.app U).hom a) := PresheafOfModules.naturality_apply i.val g.op aₛ
  have hincnat := PresheafOfModules.naturality_apply
    (annihilatorSheafInclusion f I i G).val g.op x
  change (η.app (Opposite.op V)) y =
    (annihilatorSheaf f I i G).val.map g.op x at hy
  have hkey : G.val.map g.op ((annihilatorSheafInclusion f I i G).val.app U x) = y.val :=
    hincnat.symm.trans
      ((congrArg (fun z => (annihilatorSheafInclusion f I i G).val.app (Opposite.op V) z)
        hy.symm).trans (hunit (Opposite.op V) y))
  let cg : (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj
      (Opposite.op V) :=
    (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.map g.op c
  let cb : (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj
      (Opposite.op V) :=
    i.val.app (Opposite.op V) (I.val.map g.op a)
  have hcc : cg = cb := hnat.symm
  have h0 : cb • y.val = 0 := by
    have hprop := y.property (Opposite.op V) (𝟙 (Opposite.op V)) (I.val.map g.op a)
    simp only [] at hprop
    let m : G.val.obj (Opposite.op V) := G.val.map (𝟙 (Opposite.op V)) y.val
    have hprop' : cb • m = 0 := hprop
    have hm : m = y.val := by
      change G.val.map (𝟙 (Opposite.op V)) y.val = y.val
      simp only [PresheafOfModules.map_id, ModuleCat.restrictScalarsId'_inv_app,
        ModuleCat.restrictScalarsId'App_inv_apply]
      all_goals exact rfl
    exact (congrArg (fun z => cb • z) hm.symm).trans hprop'
  exact (congrArg (fun z => cg • z) hkey).trans
    ((congrArg (fun t => t • y.val) hcc).trans h0)
private noncomputable def annihilatorSheafDescend
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (hf : Presheaf.IsLocallySurjective J f.hom)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hi_univ : ∀ (U : Cᵒᵖ) (x : O'.obj.obj U), f.hom.app U x = 0 →
      ∃! a : I.val.obj U, (show O'.obj.obj U from i.val.app U a) = x)
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')) :
    Σ N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O),
      (SheafOfModules.restrictScalars (ringMap f)).obj N ≅
        annihilatorSheaf f I i G := by
  letI : Presheaf.IsLocallySurjective J (ringMap f).hom := ⟨hf.imageSieve_mem⟩
  apply descendModule (ringMap f) _
  intro U r hr x
  obtain ⟨a, ha, _⟩ := hi_univ U r hr
  let c : (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U :=
    i.val.app U a
  have hc : c = r := ha
  have : Mono (annihilatorSheafInclusion f I i G) := annihilatorSheafInclusion_mono f I i G
  have hmono : Mono (annihilatorSheafInclusion f I i G).val := mono_val_of_mono _
  have hz : c • x = 0 := by
    apply PresheafOfModules.injective_of_mono
      (annihilatorSheafInclusion f I i G).val U
    rw [map_smul, map_zero]
    exact annihilatorSheafInclusion_smul_zero f I i G U a x
  exact (congrArg (fun t => t • x) hc.symm).trans hz
omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
private lemma tensor_pairing_balanced_of_locallySurjective
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (hf : Presheaf.IsLocallySurjective J f.hom)
    (B F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (t : MonoidalCategoryStruct.tensorObj
      ((SheafOfModules.restrictScalars (ringMap f)).obj B).val
      ((SheafOfModules.restrictScalars (ringMap f)).obj F).val ⟶ H.val)
    (U : Cᵒᵖ) (r : O.obj.obj U) (b : B.val.obj U) (x : F.val.obj U) :
    t.app U (((show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U from
      r) • b) ⊗ₜ[O'.obj.obj U] x) =
      t.app U (b ⊗ₜ[O'.obj.obj U]
        ((show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U from
          r) • x)) := by
  let r' : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U := r
  let R := SheafOfModules.restrictScalars (ringMap f)
  apply H.isSheaf.isSeparated _ _ (hf.imageSieve_mem r)
  rintro V g ⟨a, ha⟩
  let : Module (O'.obj.obj (Opposite.op V)) ((R.obj B).val.obj (Opposite.op V)) :=
    inferInstanceAs (Module
      ((Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj (Opposite.op V))
      ((R.obj B).val.obj (Opposite.op V)))
  let : Module (O'.obj.obj (Opposite.op V)) ((R.obj F).val.obj (Opposite.op V)) :=
    inferInstanceAs (Module
      ((Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj (Opposite.op V))
      ((R.obj F).val.obj (Opposite.op V)))
  let b' : (R.obj B).val.obj (Opposite.op V) := B.val.map g.op b
  let x' : (R.obj F).val.obj (Opposite.op V) := F.val.map g.op x
  change f.hom.app (Opposite.op V) a =
    (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.map g.op r' at ha
  have hz₁ : H.val.map g.op (t.app U ((r' • b) ⊗ₜ[O'.obj.obj U] x)) =
      t.app (Opposite.op V)
        (B.val.map g.op (r' • b) ⊗ₜ[O'.obj.obj (Opposite.op V)] F.val.map g.op x) :=
    (PresheafOfModules.naturality_apply t g.op _).symm
  have hz₂ : H.val.map g.op (t.app U (b ⊗ₜ[O'.obj.obj U] (r' • x))) =
      t.app (Opposite.op V)
        (B.val.map g.op b ⊗ₜ[O'.obj.obj (Opposite.op V)] F.val.map g.op (r' • x)) :=
    (PresheafOfModules.naturality_apply t g.op _).symm
  refine hz₁.trans (Eq.trans (congrArg (t.app (Opposite.op V)) ?_) hz₂.symm)
  rw [B.val.map_smul, F.val.map_smul, ← ha]
  exact TensorProduct.smul_tmul (R := O'.obj.obj (Opposite.op V)) a b' x'
private noncomputable def tensorPairingRestrictLift
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (hf : Presheaf.IsLocallySurjective J f.hom)
    (B F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (t : MonoidalCategoryStruct.tensorObj
      ((SheafOfModules.restrictScalars (ringMap f)).obj B).val
      ((SheafOfModules.restrictScalars (ringMap f)).obj F).val ⟶ H.val) :
    (PresheafOfModules.restrictScalars (ringMap f).hom).obj
      (PresheafOfModules.tensorObj B.val F.val) ⟶ H.val := by
  letI (U : Cᵒᵖ) :
      Module ((Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U)
        ((PresheafOfModules.tensorObj B.val F.val).obj U) :=
    inferInstanceAs (Module
      ((Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U)
      (((PresheafOfModules.restrictScalars (ringMap f).hom).obj
        (PresheafOfModules.tensorObj B.val F.val)).obj U))
  letI (U : Cᵒᵖ) : Module (O'.obj.obj U) (B.val.obj U) :=
    inferInstanceAs (Module
      ((Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U)
      (((SheafOfModules.restrictScalars (ringMap f)).obj B).val.obj U))
  letI (U : Cᵒᵖ) : Module (O'.obj.obj U) (F.val.obj U) :=
    inferInstanceAs (Module
      ((Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U)
      (((SheafOfModules.restrictScalars (ringMap f)).obj F).val.obj U))
  let e (U : Cᵒᵖ) : B.val.obj U →+ F.val.obj U →+ H.val.obj U :=
    { toFun := fun b =>
        { toFun := fun x => t.app U (b ⊗ₜ[O'.obj.obj U] x)
          map_zero' := by
            refine Eq.trans (congrArg (t.app U) ?_) (map_zero _)
            exact TensorProduct.tmul_zero _ b
          map_add' := by
            intro x₁ x₂
            refine Eq.trans (congrArg (t.app U) ?_) (map_add _ _ _)
            exact TensorProduct.tmul_add b x₁ x₂ }
      map_zero' := by
        ext x₀
        refine Eq.trans (congrArg (t.app U) ?_) (map_zero _)
        exact TensorProduct.zero_tmul _ x₀
      map_add' := by
        intro b₁ b₂
        ext x₀
        refine Eq.trans (congrArg (t.app U) ?_) (map_add _ _ _)
        exact TensorProduct.add_tmul b₁ b₂ x₀ }
  let p (U : Cᵒᵖ) : (PresheafOfModules.tensorObj B.val F.val).obj U →+ H.val.obj U :=
    TensorProduct.liftAddHom (e U)
      (tensor_pairing_balanced_of_locallySurjective f hf B F H t U)
  let Q := (PresheafOfModules.restrictScalars (ringMap f).hom).obj
    (PresheafOfModules.tensorObj B.val F.val)
  refine
    { app := fun U =>
        ModuleCat.ofHom (show
          Q.obj U →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U]
            H.val.obj U from
            { toFun := p U
              map_add' := (p U).map_add
              map_smul' := ?_ })
      naturality := ?_ }
  · intro r z
    induction z using TensorProduct.inductionOn with
    | tmul b x =>
      change p U ((f.hom.app U r) • (b ⊗ₜ[O.obj.obj U] x)) = r • p U _
      let b' : ((SheafOfModules.restrictScalars (ringMap f)).obj B).val.obj U := b
      let x' : ((SheafOfModules.restrictScalars (ringMap f)).obj F).val.obj U := x
      change t.app U ((r • b') ⊗ₜ[O'.obj.obj U] x') =
        r • t.app U (b' ⊗ₜ[O'.obj.obj U] x')
      exact LinearMap.map_smul (ModuleCat.Hom.hom (t.app U)) r (b' ⊗ₜ[O'.obj.obj U] x')
    | add z z' hz hz' =>
      have key : ∀ w w' : (PresheafOfModules.tensorObj B.val F.val).obj U,
          p U (r • w) = r • p U w → p U (r • w') = r • p U w' →
          p U (r • (w + w')) = r • p U (w + w') := by
        intro w w' h h'
        refine Eq.trans (congrArg (p U) (smul_add r w w')) ?_
        refine Eq.trans ((p U).map_add _ _) ?_
        refine Eq.trans (congrArg₂ (· + ·) h h') ?_
        exact (Eq.trans (congrArg (fun y => r • y) ((p U).map_add w w'))
          (smul_add r ((p U) w) ((p U) w'))).symm
      exact key z z' hz hz'
  · intro U V g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have key : ∀ {W : Type w} [AddCommMonoid W] (φ ψ : Q.obj U → W),
        (∀ u v, φ (u + v) = φ u + φ v) →
        (∀ u v, ψ (u + v) = ψ u + ψ v) →
        (∀ (b : B.val.obj U) (x : F.val.obj U),
          φ (b ⊗ₜ[O.obj.obj U] x) = ψ (b ⊗ₜ[O.obj.obj U] x)) → ∀ w, φ w = ψ w := by
      intro W _ φ ψ ha ka h w
      induction w using TensorProduct.inductionOn with
      | tmul b x => exact h b x
      | add w w' hw hw' =>
        exact (ha w w').trans ((congrArg₂ (· + ·) hw hw').trans (ka w w').symm)
    exact key _ _ (fun u v => map_add _ u v)
      (fun u v => map_add _ u v)
      (fun b x => PresheafOfModules.naturality_apply t g (b ⊗ₜ[O'.obj.obj U] x)) z
private lemma reductionTensorMap_id_isIso
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (hf : Presheaf.IsLocallySurjective J f.hom)
    (B F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    IsIso (reductionTensorMap f B
      ((SheafOfModules.restrictScalars (ringMap f)).obj F) F (𝟙 _)) := by
  let R := SheafOfModules.restrictScalars (ringMap f)
  let T := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj (R.obj F))).obj
    (R.obj B)
  let η := (PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
      Stacks.SheafOfModules.Tensor.ringSheaf
      O')
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
      (PresheafOfModules.tensorObj (R.obj B).val (R.obj F).val)
  let p := tensorPairingRestrictLift f hf B F T η
  let u := (PresheafOfModules.restrictScalars (ringMap f).hom).map
    ((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
        Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
      (PresheafOfModules.tensorObj B.val F.val))
  have : PresheafOfModules.IsLocallyInjective J u := by
    change Presheaf.IsLocallyInjective J
      (CategoryTheory.toSheafify J (PresheafOfModules.tensorObj B.val F.val).presheaf)
    infer_instance
  have : PresheafOfModules.IsLocallySurjective J u := by
    change Presheaf.IsLocallySurjective J
      (CategoryTheory.toSheafify J (PresheafOfModules.tensorObj B.val F.val).presheaf)
    infer_instance
  let e := PresheafOfModules.homEquivOfIsLocallyBijective u T.isSheaf
  let s :
      R.obj ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F)).obj B) ⟶
        T :=
    ⟨e.symm p⟩
  have hs : u ≫ s.val = p := e.apply_symm_apply p
  let a := reductionTensorMap f B (R.obj F) F (𝟙 _)
  have ha : a ≫ s = 𝟙 T := by
    apply tensorSheaf_hom_ext O' (R.obj B) (R.obj F) T
    intro U b x
    change s.val.app U ((reductionTensorMap f B
        ((SheafOfModules.restrictScalars (ringMap f)).obj F) F (𝟙 _)).val.app U
      (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf O')
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
      (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars (ringMap f)).obj B).val
          ((SheafOfModules.restrictScalars (ringMap f)).obj F).val)).app U
          (b ⊗ₜ[O'.obj.obj U] x))) = η.app U (b ⊗ₜ[O'.obj.obj U] x)
    exact (congrArg (fun y => s.val.app U y)
        (reductionTensorMap_tmul f B ((SheafOfModules.restrictScalars (ringMap f)).obj F) F
          (𝟙 _) U b x)).trans
      (congrArg (fun k => k.app U (b ⊗ₜ[O.obj.obj U] x)) hs)
  have : Epi a := reductionTensorMap_epi f B (R.obj F) F (𝟙 _)
  have : Mono a := mono_of_mono_fac ha
  exact isIso_of_mono_of_epi a
private lemma tensorLeft_multiplicationMap_eq_zero
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hi_zero : ∀ (U : Cᵒᵖ) (a : I.val.obj U),
      f.hom.app U (show O'.obj.obj U from i.val.app U a) = 0) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O')).obj
      ((SheafOfModules.restrictScalars (ringMap f)).obj B)).map
        (multiplicationMap f I G i) = 0 := by
  let R := SheafOfModules.restrictScalars (ringMap f)
  let M := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj G)).obj
    (R.obj I)
  let T := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj G)).obj
    (R.obj B)
  let η : MonoidalCategoryStruct.tensorObj (R.obj I).val G.val ⟶ M.val :=
    (PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
        Stacks.SheafOfModules.Tensor.ringSheaf O')
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
      (PresheafOfModules.tensorObj (R.obj I).val G.val)
  let τ : MonoidalCategoryStruct.tensorObj (R.obj B).val G.val ⟶ T.val :=
    (PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
        Stacks.SheafOfModules.Tensor.ringSheaf O')
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
      (PresheafOfModules.tensorObj (R.obj B).val G.val)
  apply tensorSheaf_hom_ext O' ((SheafOfModules.restrictScalars (ringMap f)).obj B)
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj G)).obj
      ((SheafOfModules.restrictScalars (ringMap f)).obj I)) T
  intro U b z
  refine Eq.trans (tensorLeft_map_tmul O' ((SheafOfModules.restrictScalars (ringMap f)).obj B)
    (multiplicationMap f I G i) U b z) ?_
  let ηp := (PresheafOfModules.toPresheaf _).map η
  have : Presheaf.IsLocallySurjective J ηp := by
    change Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J _)
    infer_instance
  apply T.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J ηp z)
  rintro V g ⟨y, hy⟩
  let : Module (O'.obj.obj (Opposite.op V)) ((R.obj B).val.obj (Opposite.op V)) :=
    inferInstanceAs (Module
      ((Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj (Opposite.op V))
      ((R.obj B).val.obj (Opposite.op V)))
  let : Module (O'.obj.obj (Opposite.op V)) (G.val.obj (Opposite.op V)) :=
    inferInstanceAs (Module
      ((Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj (Opposite.op V))
      (G.val.obj (Opposite.op V)))
  let : Module (O.obj.obj (Opposite.op V)) (B.val.obj (Opposite.op V)) :=
    inferInstanceAs (Module
      ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj (Opposite.op V))
      (B.val.obj (Opposite.op V)))
  change T.val.map g.op (τ.app U (b ⊗ₜ[O'.obj.obj U]
    (multiplicationMap f I G i).val.app U z)) = T.val.map g.op 0
  rw [map_zero]
  refine Eq.trans (PresheafOfModules.naturality_apply τ g.op (b ⊗ₜ[O'.obj.obj U]
    (multiplicationMap f I G i).val.app U z)).symm ?_
  change τ.app (Opposite.op V)
    (B.val.map g.op b ⊗ₜ[O'.obj.obj (Opposite.op V)]
      G.val.map g.op ((multiplicationMap f I G i).val.app U z)) = 0
  change η.app (Opposite.op V) y = M.val.map g.op z at hy
  refine Eq.trans (congrArg (fun w => τ.app (Opposite.op V)
      (B.val.map g.op b ⊗ₜ[O'.obj.obj (Opposite.op V)] w))
    ((PresheafOfModules.naturality_apply (multiplicationMap f I G i).val g.op z).symm.trans
      (congrArg (fun v => (multiplicationMap f I G i).val.app (Opposite.op V) v) hy).symm)) ?_
  clear hy
  induction y using TensorProduct.inductionOn with
  | tmul a x =>
    refine Eq.trans (congrArg (fun w => τ.app (Opposite.op V)
        (B.val.map g.op b ⊗ₜ[O'.obj.obj (Opposite.op V)] w))
      (multiplicationMap_tmul f I G i (Opposite.op V) a x)) ?_
    let a' : O'.obj.obj (Opposite.op V) := i.val.app (Opposite.op V) a
    let b' : (R.obj B).val.obj (Opposite.op V) := B.val.map g.op b
    change τ.app (Opposite.op V) (b' ⊗ₜ[O'.obj.obj (Opposite.op V)] (a' • x)) = 0
    have hb : a' • b' = 0 := by
      have h0 : f.hom.app (Opposite.op V) a' = 0 := hi_zero (Opposite.op V) a
      change f.hom.app (Opposite.op V) a' • (show B.val.obj (Opposite.op V) from b') = 0
      rw [h0, zero_smul]
    refine Eq.trans (congrArg (τ.app (Opposite.op V))
      (TensorProduct.smul_tmul (R := O'.obj.obj (Opposite.op V)) a' b' x).symm) ?_
    refine Eq.trans (congrArg (fun w => τ.app (Opposite.op V)
      (w ⊗ₜ[O'.obj.obj (Opposite.op V)] x)) hb) ?_
    exact (congrArg (τ.app (Opposite.op V)) (TensorProduct.zero_tmul _ x)).trans (map_zero _)
  | add y y' hy hy' =>
    have h1 : (multiplicationMap f I G i).val.app (Opposite.op V)
          (η.app (Opposite.op V) (y + y')) =
        (multiplicationMap f I G i).val.app (Opposite.op V) (η.app (Opposite.op V) y) +
          (multiplicationMap f I G i).val.app (Opposite.op V) (η.app (Opposite.op V) y') :=
      (congrArg _ (map_add _ y y')).trans (map_add _ _ _)
    refine Eq.trans (congrArg (fun w => τ.app (Opposite.op V)
      (B.val.map g.op b ⊗ₜ[O'.obj.obj (Opposite.op V)] w)) h1) ?_
    refine Eq.trans (congrArg (τ.app (Opposite.op V)) (TensorProduct.tmul_add _ _ _)) ?_
    refine Eq.trans (map_add _ _ _) ?_
    exact (congrArg₂ (· + ·) hy hy').trans (add_zero 0)

/-- If `q` exhibits `F` as the cokernel of `multiplicationMap f I G i`, then
`reductionTensorMap f B G F q` is an isomorphism `B ⊗[O'] G ≅ B ⊗[O] F`. -/
lemma reductionTensorMap_isIso
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (hf : Presheaf.IsLocallySurjective J f.hom)
    (I B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hi_zero : ∀ (U : Cᵒᵖ) (a : I.val.obj U),
      f.hom.app U (show O'.obj.obj U from i.val.app U a) = 0)
    (q : G ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj F)
    (hz : multiplicationMap f I G i ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q hz)) :
    IsIso (reductionTensorMap f B G F q) := by
  let R := SheafOfModules.restrictScalars (ringMap f)
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O')).obj (R.obj B)
  have := tensorLeft_preservesColimits O' (R.obj B)
  let S := ShortComplex.mk (multiplicationMap f I G i) q hz
  have he : (S.map T).Exact :=
    (S.exact_of_g_is_cokernel hq).map_of_epi_of_preservesCokernel T
      (Cofork.IsColimit.epi hq) inferInstance
  have : Epi q := Cofork.IsColimit.epi hq
  have : Epi (T.map q) := inferInstance
  have : Mono (T.map q) := he.mono_g (tensorLeft_multiplicationMap_eq_zero f I B G i hi_zero)
  have hTq : IsIso (T.map q) := isIso_of_mono_of_epi _
  have hrid : IsIso (reductionTensorMap f B (R.obj F) F (𝟙 _)) :=
    reductionTensorMap_id_isIso f hf B F
  have h : T.map q ≫ reductionTensorMap f B (R.obj F) F (𝟙 _) =
      reductionTensorMap f B G F q := by
    have hn := reductionTensorMap_natural_right f B q (𝟙 _) q (𝟙 F) (by simp)
    have hid := ((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj B).map_id F
    have hr := R.map_id (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj B).obj F)
    exact hn.trans ((congrArg (fun a => reductionTensorMap f B G F q ≫ R.map a) hid).trans
      ((congrArg (fun a => reductionTensorMap f B G F q ≫ a) hr).trans
        (Category.comp_id _)))
  rw [← h]
  infer_instance
private lemma flat_tensorLeft_preserves_mono
    (O : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat F)
    {A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (g : A ⟶ B) [Mono g] :
    Mono (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj F).map g) := by
  have : Mono ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F)).map g) :=
    flat_tensor_preserves_mono O F hF g
  exact mono_of_mono_fac ((tensorLeftIsoTensorRight O F).hom.naturality g)

private lemma tensorRight_map_mono_of_flat_cokernel
    (O : Sheaf J CommRingCat.{w})
    (S : ShortComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (hS : S.ShortExact) (hF : AlgebraicGeometry.SheafOfModules.IsFlat S.X₃)
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    Mono ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj N)).map S.f) := by
  obtain ⟨Q, p, hQ, hp⟩ := Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat O N
  let k := kernel.ι p
  let E := ShortComplex.mk k p (kernel.condition p)
  have hE : E.ShortExact := ⟨E.exact_of_f_is_kernel (kernelIsKernel p)⟩
  have : Epi E.g := hE.epi_g
  let K := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj (kernel p))
  let P := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj Q)
  let T := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj N)
  let a := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.map k
  let b := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.map p
  let φ : S.map K ⟶ S.map P := S.mapNatTrans a
  have : Mono S.f := hS.mono_f
  have : Mono (S.map P).f := flat_tensor_preserves_mono O Q hQ S.f
  have : Mono φ.τ₃ := flat_tensorLeft_preserves_mono O S.X₃ hF k
  have : Mono (cokernel.map φ.τ₁ φ.τ₂ (S.map K).f (S.map P).f φ.comm₁₂) :=
    mono_cokernelMap_of_exact_of_mono φ
      (hS.exact.map_of_epi_of_preservesCokernel K hS.epi_g inferInstance)
  exact mono_of_mono_cokernelMap φ.comm₁₂ (b.app S.X₁) (b.app S.X₂) (T.map S.f)
    (E.map ((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj S.X₁)).zero
    (E.map ((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj S.X₂)).zero
    (isColimit_map_tensorLeft O hE S.X₁) (isColimit_map_tensorLeft O hE S.X₂)
    (b.naturality S.f).symm

private lemma tensorLeft_map_mono_of_flat_cokernel
    (O : Sheaf J CommRingCat.{w})
    (S : ShortComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (hS : S.ShortExact) (hF : AlgebraicGeometry.SheafOfModules.IsFlat S.X₃)
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    Mono (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj N).map S.f) := by
  have := tensorRight_map_mono_of_flat_cokernel O S hS hF N
  exact mono_of_mono_fac ((tensorLeftIsoTensorRight O N).hom.naturality S.f)

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
private lemma restrictScalars_map_mono
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    {A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (g : A ⟶ B) [Mono g] :
    Mono ((SheafOfModules.restrictScalars (ringMap f)).map g) := by
  apply (SheafOfModules.toSheaf
    (Stacks.SheafOfModules.Tensor.ringSheaf O')).mono_of_mono_map
  change Mono ((SheafOfModules.toSheaf
    (Stacks.SheafOfModules.Tensor.ringSheaf O)).map g)
  infer_instance

private noncomputable def cokernelCoforkCompIso
    {D : Type*} [Category D] [HasZeroMorphisms D]
    {X Y Q Q' : D} {l : X ⟶ Y} {p : Y ⟶ Q} {h : l ≫ p = 0}
    (hp : IsColimit (CokernelCofork.ofπ p h)) (e : Q ≅ Q') :
    IsColimit (CokernelCofork.ofπ (f := l) (p ≫ e.hom)
      (by rw [← Category.assoc, h, Limits.zero_comp])) := by
  have : Epi p := Cofork.IsColimit.epi hp
  refine CokernelCofork.IsColimit.ofπ' _ _ (fun k hk => ?_)
  obtain ⟨a, ha⟩ := CokernelCofork.IsColimit.desc' hp k hk
  exact ⟨e.inv ≫ a, by simpa using ha⟩

/-- The reduction `F'/IF'`, as a cokernel of `multiplicationMap`, with its quotient map. -/
private noncomputable def reductionOfMultiplication
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (hf : Presheaf.IsLocallySurjective J f.hom)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hi_univ : ∀ (U : Cᵒᵖ) (x : O'.obj.obj U), f.hom.app U x = 0 →
      ∃! a : I.val.obj U, (show O'.obj.obj U from i.val.app U a) = x)
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')) :
    Σ' (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (q : G ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj F)
      (hz : multiplicationMap f I G i ≫ q = 0), IsColimit (CokernelCofork.ofπ q hz) :=
  let d := multiplicationCokernelDescend f hf I i hi_univ G
  ⟨d.1, cokernel.π _ ≫ d.2.inv, (cokernel.condition_assoc _ d.2.inv).trans zero_comp,
    cokernelCoforkCompIso (h := cokernel.condition _) (cokernelIsCokernel _) d.2.symm⟩

private noncomputable def changeOfRings_unit_isCokernel
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (hf : Presheaf.IsLocallySurjective J f.hom)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hi_zero : ∀ (U : Cᵒᵖ) (a : I.val.obj U),
      f.hom.app U (show O'.obj.obj U from i.val.app U a) = 0)
    (hi_univ : ∀ (U : Cᵒᵖ) (x : O'.obj.obj U), f.hom.app U x = 0 →
      ∃! a : I.val.obj U, (show O'.obj.obj U from i.val.app U a) = x)
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')) :
    IsColimit (CokernelCofork.ofπ
      (C := SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
      ((Stacks.FlatChangeOfRings.extendScalarsAdjunction f).unit.app G)
      (multiplicationMap_comp_restrictScalars f I G i hi_zero _ _)) := by
  let R := SheafOfModules.restrictScalars (ringMap f)
  obtain ⟨F, q, hz, hq⟩ := reductionOfMultiplication f hf I i hi_univ G
  let e := reductionIsoChangeOfRings f hf I G F i hi_zero q hz hq
  let adj := Stacks.FlatChangeOfRings.extendScalarsAdjunction f
  have he : q ≫ R.map e.hom = adj.unit.app G := by
    dsimp only [e, reductionIsoChangeOfRings, R]
    refine (congrArg (fun morphism => q ≫ morphism)
      ((restrictScalarsFullyFaithful f hf).map_preimage
        (X := F) (Y := (Stacks.FlatChangeOfRings.extendScalars f).obj G) _)).trans ?_
    exact (CokernelCofork.IsColimit.desc' hq (adj.unit.app G)
      (multiplicationMap_comp_restrictScalars f I G i hi_zero _ _)).2
  exact IsColimit.ofIsoColimit hq (Cofork.ext (R.mapIso e) he)

/-- Given a commutative square `q ≫ k = g ≫ r`, if `reductionTensorMap f B G F q` and the
restriction of `B ⊗ k` are monomorphisms, then so is `B ⊗ g` over `O'`. -/
private lemma mono_tensorLeft_map_of_reductionTensorMap
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {G H : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')}
    {F K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (q : G ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj F)
    (r : H ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj K)
    (g : G ⟶ H) (k : F ⟶ K)
    (comm : q ≫ (SheafOfModules.restrictScalars (ringMap f)).map k = g ≫ r)
    (hq : Mono (reductionTensorMap f B G F q))
    (hk : Mono ((SheafOfModules.restrictScalars (ringMap f)).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj B).map k))) :
    Mono (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O')).obj
      ((SheafOfModules.restrictScalars (ringMap f)).obj B)).map g) :=
  @mono_of_mono_fac _ _ _ _ _ _ _ _ (mono_comp' hq hk)
    (reductionTensorMap_natural_right f B q r g k comm)
private lemma tensorLeft_map_mono_of_reduction_flat
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (hf : Presheaf.IsLocallySurjective J f.hom)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hi_zero : ∀ (U : Cᵒᵖ) (a : I.val.obj U),
      f.hom.app U (show O'.obj.obj U from i.val.app U a) = 0)
    (hi_univ : ∀ (U : Cᵒᵖ) (x : O'.obj.obj U), f.hom.app U x = 0 →
      ∃! a : I.val.obj U, (show O'.obj.obj U from i.val.app U a) = x)
    (S : ShortComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O')))
    (hS : S.ShortExact) (hm : Mono (multiplicationMap f I S.X₃ i))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat
      ((Stacks.FlatChangeOfRings.extendScalars f).obj S.X₃))
    (B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    Mono (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O')).obj
      ((SheafOfModules.restrictScalars (ringMap f)).obj B)).map S.f) := by
  let R := SheafOfModules.restrictScalars (ringMap f)
  let E : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O') ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
    Stacks.FlatChangeOfRings.extendScalars f
  let adj := Stacks.FlatChangeOfRings.extendScalarsAdjunction f
  let η := adj.unit
  have : E.IsLeftAdjoint := adj.isLeftAdjoint
  have : R.Additive := SheafOfModules.instAdditiveRestrictScalars (ringMap f)
  have : E.Additive := adj.left_adjoint_additive
  have : E.PreservesZeroMorphisms := @Functor.preservesZeroMorphisms_of_additive
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) _ _ _ _ E
      (adj.left_adjoint_additive)
  have : R.Faithful := (restrictScalarsFullyFaithful f hf).faithful
  have hcol (G : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf O')) :=
    changeOfRings_unit_isCokernel f hf I i hi_zero hi_univ G
  have hzero (G : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf O')) :=
    multiplicationMap_comp_restrictScalars f I G i hi_zero (E.obj G) (η.app G)
  have : Mono (cokernel.map (multiplicationMap f I S.X₁ i)
      (multiplicationMap f I S.X₂ i) (tensorSecondSheafMap f S.f) S.f
      (multiplicationMap_natural f I i S.f)) :=
    reduction_kernel_map_mono f I i S hS hm
  have : Mono (R.map (E.map S.f)) :=
    mono_of_mono_cokernelMap (multiplicationMap_natural f I i S.f)
      (η.app S.X₁) (η.app S.X₂) (R.map (E.map S.f))
      (hzero S.X₁) (hzero S.X₂) (hcol S.X₁) (hcol S.X₂)
      (η.naturality S.f).symm
  have : Mono (E.map S.f) := R.mono_of_mono_map inferInstance
  have : Epi S.g := hS.epi_g
  have : Mono (S.map E).f := ‹Mono (E.map S.f)›
  have : Epi (S.map E).g := by
    change Epi (E.map S.g)
    infer_instance
  have hSE : (S.map E).ShortExact :=
    ⟨hS.exact.map_of_epi_of_preservesCokernel E hS.epi_g inferInstance⟩
  have : Mono (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj B).map (E.map S.f)) :=
    tensorLeft_map_mono_of_flat_cokernel O (S.map E) hSE hF B
  have h2 : Mono ((SheafOfModules.restrictScalars (ringMap f)).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj B).map (E.map S.f))) :=
    restrictScalars_map_mono f _
  have hcomp (G : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf O')) :
      IsIso (reductionTensorMap f B G (E.obj G) (η.app G)) :=
    reductionTensorMap_isIso f hf I B G (E.obj G) i hi_zero (η.app G)
      (hzero G) (hcol G)
  have h1 : Mono (reductionTensorMap f B S.X₁ (E.obj S.X₁) (η.app S.X₁)) :=
    have := hcomp S.X₁
    inferInstance
  exact mono_tensorLeft_map_of_reductionTensorMap f B
    (G := S.X₁) (H := S.X₂) (F := E.obj S.X₁) (K := E.obj S.X₂)
    (η.app S.X₁) (η.app S.X₂) S.f (E.map S.f) (η.naturality S.f).symm h1 h2
omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
private lemma tensorLeft_map_mono_of_iso
    (O : Sheaf J CommRingCat.{w})
    {A B L P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (e : A ≅ B) (l : L ⟶ P)
    (h : Mono (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj A).map l)) :
    Mono (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj B).map l) := by
  let t := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).mapIso e
  exact mono_of_mono_fac (t.inv.naturality l)

/-- Flatness over a square-zero thickening is equivalent to flatness of the reduction and
injectivity of the canonical multiplication map from the kernel tensored with the reduction.

Here `i` identifies `I` with the kernel of `f`, `nu` is multiplication
`I ⊗[O'] F' ⟶ F'`, and `q` exhibits `F` as its cokernel.  The last
displayed formula identifies `mu` with the canonical map
`I ⊗[O] F ⟶ F'`. -/
@[stacks 08M4]
public theorem isFlat_iff_reduction_isFlat_and_multiplication_mono
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (hf : Presheaf.IsLocallySurjective J f.hom)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hi_zero : ∀ (U : Cᵒᵖ) (a : I.val.obj U),
      f.hom.app U (show O'.obj.obj U from i.val.app U a) = 0)
    (hi_univ : ∀ (U : Cᵒᵖ) (x : O'.obj.obj U), f.hom.app U x = 0 →
      ∃! a : I.val.obj U, (show O'.obj.obj U from i.val.app U a) = x)
    (hsq : ∀ (U : Cᵒᵖ) (a b : I.val.obj U),
      (show O'.obj.obj U from i.val.app U a) *
        (show O'.obj.obj U from i.val.app U b) = 0)
    (nu : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj F')).obj
        ((SheafOfModules.restrictScalars (ringMap f)).obj I) ⟶ F')
    (hnu : ∀ (U : Cᵒᵖ) (a : I.val.obj U) (x : F'.val.obj U),
      nu.val.app U
          (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
              Stacks.SheafOfModules.Tensor.ringSheaf
              O')
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
      (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars (ringMap f)).obj I).val
          F'.val)).app U
              (a ⊗ₜ[O'.obj.obj U] x)) =
        (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
          i.val.app U a) • x)
    (q : F' ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj F)
    (hnuq : nu ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q hnuq))
    (mu : (SheafOfModules.restrictScalars (ringMap f)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F)).obj I) ⟶ F')
    (hmu : ∀ (U : Cᵒᵖ) (a : I.val.obj U) (x : F'.val.obj U),
      mu.val.app U
          (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
              Stacks.SheafOfModules.Tensor.ringSheaf
              O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
      (PresheafOfModules.tensorObj I.val F.val)).app U
            (a ⊗ₜ[O.obj.obj U] q.val.app U x)) =
        (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
          i.val.app U a) • x) :
    AlgebraicGeometry.SheafOfModules.IsFlat F' ↔
      (AlgebraicGeometry.SheafOfModules.IsFlat F ∧ Mono mu) := by
  have hnu_eq := multiplicationMap_eq_of_tmul f I F' i nu hnu
  subst nu
  have hmul : reductionTensorMap f I F' F q ≫ mu = multiplicationMap f I F' i := by
    apply multiplicationMap_eq_of_tmul f I F' i
    intro U a x
    change mu.val.app U ((reductionTensorMap f I F' F q).val.app U _) = _
    rw [reductionTensorMap_tmul]
    exact hmu U a x
  constructor
  · intro hflat
    refine ⟨?_, ?_⟩
    · exact isFlat_of_iso (reductionIsoChangeOfRings f hf I F' F i hi_zero q hnuq hq).symm
        (Stacks.FlatChangeOfRings.isFlat_extendScalars f F' hflat)
    · have : Mono i := kernelMap_mono f I i hi_zero hi_univ
      have : Mono (multiplicationMap f I F' i) :=
        multiplicationMap_mono_of_flat f I F' i hflat
      have : Epi q := Cofork.IsColimit.epi hq
      have ht : Epi (reductionTensorMap f I F' F q) := reductionTensorMap_epi f I F' F q
      have hm := mono_of_mono_fac hmul
      have : IsIso (reductionTensorMap f I F' F q) :=
        isIso_of_mono_of_epi (reductionTensorMap f I F' F q)
      apply (mono_comp_iff_of_isIso (reductionTensorMap f I F' F q) mu).mp
      rw [hmul]
      infer_instance
  · intro hflat
    obtain ⟨P, p, hP, hp⟩ := Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat O' F'
    let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    have hS : S.ShortExact := ⟨S.exact_of_f_is_kernel (kernelIsKernel p)⟩
    apply isFlat_of_pure_presentation O' S hS hP
    have hEflat : AlgebraicGeometry.SheafOfModules.IsFlat
        ((Stacks.FlatChangeOfRings.extendScalars f).obj F') :=
      isFlat_of_iso (reductionIsoChangeOfRings f hf I F' F i hi_zero q hnuq hq)
        hflat.1
    have : Mono mu := hflat.2
    have : IsIso (reductionTensorMap f I F' F q) :=
      reductionTensorMap_isIso f hf I I F' F i hi_zero q hnuq hq
    have hmono : Mono (multiplicationMap f I F' i) := by
      rw [← hmul]
      infer_instance
    intro N
    let j := annihilatorSheafInclusion f I i N
    have : Mono j := annihilatorSheafInclusion_mono f I i N
    let T := ShortComplex.mk j (cokernel.π j) (cokernel.condition j)
    have hT : T.ShortExact := ⟨T.exact_of_g_is_cokernel (cokernelIsCokernel j)⟩
    let A := annihilatorSheafDescend f hf I i hi_univ N
    let B := annihilatorCokernelDescend f hf I i hi_univ N hsq
    apply tensorLeft_map_mono_of_shortExact O' S.f hP T hT
    · exact tensorLeft_map_mono_of_iso O' A.2 S.f
        (tensorLeft_map_mono_of_reduction_flat f hf I i hi_zero hi_univ S hS hmono
          hEflat A.1)
    · exact tensorLeft_map_mono_of_iso O' B.2 S.f
        (tensorLeft_map_mono_of_reduction_flat f hf I i hi_zero hi_univ S hS hmono
          hEflat B.1)

/-- For a locally surjective morphism `f : O' ⟶ O` of sheaves of commutative rings with kernel
`I` and any `O'`-module `F'`, there are a reduction `F = F'/IF'`, exhibited as a cokernel, and
multiplication maps `I ⊗[O'] F' ⟶ F'` and `I ⊗[O] F ⟶ F'` taking the expected values on pure
tensors. -/
theorem exists_reduction_and_multiplicationMaps
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (hf : Presheaf.IsLocallySurjective J f.hom)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (hi_zero : ∀ (U : Cᵒᵖ) (a : I.val.obj U),
      f.hom.app U (show O'.obj.obj U from i.val.app U a) = 0)
    (hi_univ : ∀ (U : Cᵒᵖ) (x : O'.obj.obj U), f.hom.app U x = 0 →
      ∃! a : I.val.obj U, (show O'.obj.obj U from i.val.app U a) = x) :
    ∃ (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (nu : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj F')).obj
          ((SheafOfModules.restrictScalars (ringMap f)).obj I) ⟶ F')
      (q : F' ⟶ (SheafOfModules.restrictScalars (ringMap f)).obj F)
      (hnuq : nu ≫ q = 0) (_ : IsColimit (CokernelCofork.ofπ q hnuq))
      (mu : (SheafOfModules.restrictScalars (ringMap f)).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F)).obj I) ⟶ F'),
      (∀ (U : Cᵒᵖ) (a : I.val.obj U) (x : F'.val.obj U),
        nu.val.app U
            (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
                Stacks.SheafOfModules.Tensor.ringSheaf O')
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
      (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars (ringMap f)).obj I).val
          F'.val)).app U
                (a ⊗ₜ[O'.obj.obj U] x)) =
          (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
            i.val.app U a) • x) ∧
      (∀ (U : Cᵒᵖ) (a : I.val.obj U) (x : F'.val.obj U),
        mu.val.app U
            (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
                Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
      (PresheafOfModules.tensorObj I.val F.val)).app U
              (a ⊗ₜ[O.obj.obj U] q.val.app U x)) =
          (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
            i.val.app U a) • x) := by
  let nu := multiplicationMap f I F' i
  obtain ⟨F, q, hz, hq⟩ := reductionOfMultiplication f hf I i hi_univ F'
  have hiso : IsIso (reductionTensorMap f I F' F q) :=
    reductionTensorMap_isIso f hf I I F' F i hi_zero q hz hq
  refine ⟨F, nu, q, hz, hq,
    CategoryTheory.inv (reductionTensorMap f I F' F q) ≫ nu,
    multiplicationMap_tmul f I F' i, ?_⟩
  have hcomp : reductionTensorMap f I F' F q ≫
      (CategoryTheory.inv (reductionTensorMap f I F' F q) ≫ nu) = nu := by
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  intro U a x
  rw [← reductionTensorMap_tmul f I F' F q U a x]
  change (reductionTensorMap f I F' F q ≫
    (CategoryTheory.inv (reductionTensorMap f I F' F q) ≫ nu)).val.app U _ = _
  rw [hcomp]
  exact multiplicationMap_tmul f I F' i U a x

/-- Two morphisms `I ⊗[O'] G ⟶ G` sending the image of every pure tensor `a ⊗ x` to `i a • x`
are equal. -/
theorem multiplicationMap_unique
    {O' O : Sheaf J CommRingCat.{w}} (f : O' ⟶ O)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (i : (SheafOfModules.restrictScalars (ringMap f)).obj I ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
    (nu nu' : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O').flip.obj G)).obj
        ((SheafOfModules.restrictScalars (ringMap f)).obj I) ⟶ G)
    (hnu : ∀ (U : Cᵒᵖ) (a : I.val.obj U) (x : G.val.obj U),
      nu.val.app U
          (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
              Stacks.SheafOfModules.Tensor.ringSheaf
              O')
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
      (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars (ringMap f)).obj I).val
          G.val)).app U
              (a ⊗ₜ[O'.obj.obj U] x)) =
        (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
          i.val.app U a) • x)
    (hnu' : ∀ (U : Cᵒᵖ) (a : I.val.obj U) (x : G.val.obj U),
      nu'.val.app U
          (((PresheafOfModules.sheafificationAdjunction.{w, v, w, u} (R :=
              Stacks.SheafOfModules.Tensor.ringSheaf
              O')
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O').obj)).unit.app
      (PresheafOfModules.tensorObj ((SheafOfModules.restrictScalars (ringMap f)).obj I).val
          G.val)).app U
              (a ⊗ₜ[O'.obj.obj U] x)) =
        (show (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U from
          i.val.app U a) • x) :
    nu = nu' :=
  (multiplicationMap_eq_of_tmul f I G i nu hnu).trans
    (multiplicationMap_eq_of_tmul f I G i nu' hnu').symm

end Stacks.SheafOfModules.FlatSquareZero
