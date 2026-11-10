module

public import StacksFrontier.Algebra.Category.CommAlgCat.CoconeOfRingCocone
public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.CommAlgCat.FilteredColimits
public import StacksFrontier.Algebra.Module.Adequate.Defs
public import StacksFrontier.RingTheory.Module.FinitePresentation.Factorization

/-!
# Adequate functors and filtered colimits

An adequate functor commutes with the filtered colimits of algebras, and every adequate functor
is a pointwise quotient of a direct sum of linearly adequate functors.

## Main results

* `isColimit_mapCocone_of_isAdequate`: an adequate functor sends filtered colimits of
  commutative algebras to colimits of its underlying additive groups.
* `exists_coproduct_linearlyAdequate_surjective`: an adequate functor is a pointwise quotient of
  a direct sum of linearly adequate functors.

## References

* [Stacks Project, Tag 06UU](https://stacks.math.columbia.edu/tag/06UU)
* [Stacks Project, Tag 06UX](https://stacks.math.columbia.edu/tag/06UX)
-/

@[expose] public section

namespace AdequateFunctor

section

open CategoryTheory CategoryTheory.Limits

universe i j w v u


/-- The forgetful functor from commutative `A`-algebras to commutative rings preserves filtered
colimits, even when the carrier and base ring universes differ. -/
private noncomputable def isColimit_forget₂_commAlgCat
    {A : Type u} [CommRing A] {I : Type i} [Category.{j} I] [IsFiltered I]
    {D : I ⥤ CommAlgCat.{max u v} A} {c : Cocone D} (hc : IsColimit c) :
    IsColimit ((forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}).mapCocone c) where
  desc s := by
    let j : I := IsFiltered.nonempty.some
    exact (forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}).map
      (hc.desc (Stacks.CommAlgCat.commAlgCoconeOfRingCocone s j))
  fac s k := by
    let j : I := IsFiltered.nonempty.some
    change (forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}).map
      (c.ι.app k ≫ hc.desc (Stacks.CommAlgCat.commAlgCoconeOfRingCocone s j)) = _
    rw [hc.fac]
    rfl
  uniq s m hm := by
    let j : I := IsFiltered.nonempty.some
    let s' := Stacks.CommAlgCat.commAlgCoconeOfRingCocone s j
    let : Algebra A s.pt := (s.ι.app j).hom.comp (algebraMap A (D.obj j)) |>.toAlgebra
    let m' : c.pt ⟶ s'.pt := CommAlgCat.ofHom
      { __ := m.hom
        commutes' r := by
          change m.hom (algebraMap A c.pt r) = s.ι.app j (algebraMap A (D.obj j) r)
          have hh := ConcreteCategory.congr_hom (hm j) (algebraMap A (D.obj j) r)
          have hcj := (c.ι.app j).hom.commutes r
          calc
            m.hom (algebraMap A c.pt r) =
                m.hom ((c.ι.app j).hom (algebraMap A (D.obj j) r)) :=
              congrArg m.hom hcj.symm
            _ = s.ι.app j (algebraMap A (D.obj j) r) := by simpa using hh }
    have heq : m' = hc.desc s' := hc.uniq s' m' (fun k => by
      apply (forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}).map_injective
      change (forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}).map (c.ι.app k) ≫ m =
        s.ι.app k
      exact hm k)
    change m = (forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}).map (hc.desc s')
    have hm' : (forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}).map m' = m := by
      ext x
      rfl
    exact hm'.symm.trans (congrArg _ heq)

private noncomputable def tensorColimitRep {A : Type u} [CommRing A] {I : Type i}
    [Category.{j} I] [IsFiltered I] {D : I ⥤ CommAlgCat.{max u v} A} {c : Cocone D}
    (hc : IsColimit c) (b : c.pt) : Σ k : I, D.obj k :=
  ⟨Classical.choose (CommAlgCat.exists_app_eq hc b),
    Classical.choose (Classical.choose_spec (CommAlgCat.exists_app_eq hc b))⟩

private theorem tensorColimitRep_spec {A : Type u} [CommRing A] {I : Type i}
    [Category.{j} I] [IsFiltered I] {D : I ⥤ CommAlgCat.{max u v} A} {c : Cocone D}
    (hc : IsColimit c) (b : c.pt) :
    (c.ι.app (tensorColimitRep hc b).1).hom (tensorColimitRep hc b).2 = b :=
  Classical.choose_spec (Classical.choose_spec (CommAlgCat.exists_app_eq hc b))

/-- The additive-group-valued functor underlying extension of scalars by a fixed module. -/
private abbrev moduleExtensionAddGroupFunctor {A : Type u} [CommRing A]
    (M : ModuleCat.{max u v w} A) : CommAlgCat.{max u v} A ⥤ AddCommGrpCat.{max u v w} where
  obj B := AddCommGrpCat.of (TensorProduct A (B : Type max u v) (M : Type max u v w))
  map f := AddCommGrpCat.ofHom
    (TensorProduct.map f.hom.toLinearMap LinearMap.id).toAddMonoidHom
  map_id B := by
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul b m => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  map_comp f g := by
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul b m => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Equality of two representatives in a filtered algebra colimit remains equality after tensoring
with a fixed module and applying any additive cocone. -/
private theorem tensorCocone_rep_eq {A : Type u} [CommRing A] {I : Type i}
    [Category.{j} I] [IsFiltered I]
    [UnivLE.{i, max u v}] [UnivLE.{j, max u v}]
    {D : I ⥤ CommAlgCat.{max u v} A} {c : Cocone D}
    (hc : IsColimit c) (M : ModuleCat.{max u v w} A)
    (s : Cocone (D ⋙ moduleExtensionAddGroupFunctor M))
    {i j : I} (x : D.obj i) (y : D.obj j)
    (h : (c.ι.app i).hom x = (c.ι.app j).hom y) (m : M) :
    (s.ι.app i).hom (x ⊗ₜ[A] m) = (s.ι.app j).hom (y ⊗ₜ[A] m) := by
  let : PreservesFilteredColimitsOfSize.{j, i} (forget CommRingCat.{max u v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v, max u v, j, i}
      (forget CommRingCat.{max u v})
  let : PreservesColimitsOfShape I (forget CommRingCat.{max u v}) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits I
  let cR := (forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}).mapCocone c
  have hcR : IsColimit cR := isColimit_forget₂_commAlgCat hc
  let R := D ⋙ forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq R hcR x y h
  have h₁ := ConcreteCategory.congr_hom (s.w f) (x ⊗ₜ[A] m)
  have h₂ := ConcreteCategory.congr_hom (s.w g) (y ⊗ₜ[A] m)
  calc
    (s.ι.app i).hom (x ⊗ₜ[A] m) =
        (s.ι.app k).hom ((D.map f).hom x ⊗ₜ[A] m) := h₁.symm
    _ = (s.ι.app k).hom ((D.map g).hom y ⊗ₜ[A] m) :=
      congrArg (fun z : D.obj k => (s.ι.app k).hom (z ⊗ₜ[A] m)) hfg
    _ = (s.ι.app j).hom (y ⊗ₜ[A] m) := h₂

/-- The bilinear pairing from a filtered algebra colimit and a fixed module into the point
of an arbitrary cocone of their tensor products. -/
private noncomputable def tensorCoconeBilinearMap {A : Type u} [CommRing A] {I : Type i}
    [Category.{j} I] [IsFiltered I]
    [UnivLE.{i, max u v}] [UnivLE.{j, max u v}]
    {D : I ⥤ CommAlgCat.{max u v} A} {c : Cocone D}
    (hc : IsColimit c) (M : ModuleCat.{max u v w} A)
    (s : Cocone (D ⋙ moduleExtensionAddGroupFunctor M)) :
    c.pt →+ (M →+ s.pt) where
  toFun b := by
    let r := tensorColimitRep hc b
    exact
      { toFun := fun m => ConcreteCategory.hom (s.ι.app r.1) (r.2 ⊗ₜ[A] m)
        map_zero' := by
          rw [TensorProduct.tmul_zero]
          exact map_zero (ConcreteCategory.hom (s.ι.app r.1))
        map_add' := by
          intro x y
          rw [TensorProduct.tmul_add, map_add] }
  map_zero' := by
    let : AddCommGroup (c.pt : Type max u v) := inferInstance
    let : AddCommGroup s.pt.carrier := s.pt.str
    ext m
    let r := tensorColimitRep hc (0 : c.pt)
    let k : I := IsFiltered.nonempty.some
    have hr := tensorColimitRep_spec hc (0 : c.pt)
    have hrep : (c.ι.app r.1).hom r.2 = (c.ι.app k).hom 0 := by simpa using hr
    have h := tensorCocone_rep_eq hc M s r.2 0 hrep m
    change ConcreteCategory.hom (s.ι.app r.1) (r.2 ⊗ₜ[A] m) = 0
    simpa using h
  map_add' b b' := by
    let : AddCommGroup (c.pt : Type max u v) := inferInstance
    let : AddCommGroup s.pt.carrier := s.pt.str
    ext m
    let r := tensorColimitRep hc b
    let r' := tensorColimitRep hc b'
    let k := IsFiltered.max r.1 r'.1
    let f := IsFiltered.leftToMax r.1 r'.1
    let g := IsFiltered.rightToMax r.1 r'.1
    let z := (D.map f).hom r.2 + (D.map g).hom r'.2
    have hr := tensorColimitRep_spec hc b
    have hr' := tensorColimitRep_spec hc b'
    have hz : (c.ι.app k).hom z = b + b' := by
      change (c.ι.app k).hom ((D.map f).hom r.2 + (D.map g).hom r'.2) = b + b'
      rw [map_add]
      have hrf : (c.ι.app k).hom ((D.map f).hom r.2) = b :=
        (ConcreteCategory.congr_hom (c.w f) r.2).trans hr
      have hrg : (c.ι.app k).hom ((D.map g).hom r'.2) = b' :=
        (ConcreteCategory.congr_hom (c.w g) r'.2).trans hr'
      rw [hrf, hrg]
    let r'' := tensorColimitRep hc (b + b')
    have hr'' := tensorColimitRep_spec hc (b + b')
    have hr''z : (c.ι.app r''.1).hom r''.2 = (c.ι.app k).hom z := hr''.trans hz.symm
    have hsum := tensorCocone_rep_eq hc M s r''.2 z hr''z m
    have h₁ := tensorCocone_rep_eq hc M s r.2 ((D.map f).hom r.2)
      (ConcreteCategory.congr_hom (c.w f) r.2).symm m
    have h₂ := tensorCocone_rep_eq hc M s r'.2 ((D.map g).hom r'.2)
      (ConcreteCategory.congr_hom (c.w g) r'.2).symm m
    let a : (s.pt : Type (max u v w)) :=
      ConcreteCategory.hom (s.ι.app r.1) (r.2 ⊗ₜ[A] m)
    let a' : (s.pt : Type (max u v w)) :=
      ConcreteCategory.hom (s.ι.app r'.1) (r'.2 ⊗ₜ[A] m)
    change ConcreteCategory.hom (s.ι.app r''.1) (r''.2 ⊗ₜ[A] m) =
      a + a'
    rw [hsum]
    simp only [z, TensorProduct.add_tmul, map_add]
    rw [h₁.symm, h₂.symm]

/-- The canonical cocone on the tensor extensions of a filtered algebra diagram is a colimit
cocone whenever the algebra cocone is a colimit. -/
private noncomputable def moduleExtensionAddGroupCocone {A : Type u} [CommRing A]
    {I : Type i} [Category.{j} I] {D : I ⥤ CommAlgCat.{max u v} A}
    (c : Cocone D) (M : ModuleCat.{max u v w} A) :
    Cocone (D ⋙ moduleExtensionAddGroupFunctor M) where
  pt := AddCommGrpCat.of (TensorProduct A (c.pt : Type max u v) (M : Type max u v w))
  ι.app k := AddCommGrpCat.ofHom
    (TensorProduct.map (c.ι.app k).hom.toLinearMap LinearMap.id).toAddMonoidHom
  ι.naturality k l f := by
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul b m =>
      change (c.ι.app l).hom ((D.map f).hom b) ⊗ₜ[A] m =
        (c.ι.app k).hom b ⊗ₜ[A] m
      exact congrArg (fun z => z ⊗ₜ[A] m) (ConcreteCategory.congr_hom (c.w f) b)
    | add x y hx hy => rw [map_add, map_add, hx, hy]

private theorem tensorCoconeBilinearMap_balance {A : Type u} [CommRing A] {I : Type i}
    [Category.{j} I] [IsFiltered I]
    [UnivLE.{i, max u v}] [UnivLE.{j, max u v}] {D : I ⥤ CommAlgCat.{max u v} A} {c : Cocone D}
    (hc : IsColimit c) (M : ModuleCat.{max u v w} A)
    
    (s : Cocone (D ⋙ moduleExtensionAddGroupFunctor M)) (a : A) (b : c.pt) (m : M) :
    tensorCoconeBilinearMap hc M s (a • b) m =
      tensorCoconeBilinearMap hc M s b (a • m) := by
  let r := tensorColimitRep hc b
  let y : D.obj r.1 := a • r.2
  have hy : (c.ι.app r.1).hom y = a • b := by
    change (c.ι.app r.1).hom (a • r.2) = a • b
    rw [map_smul, tensorColimitRep_spec hc b]
  let r' := tensorColimitRep hc (a • b)
  have heq := tensorCocone_rep_eq hc M s r'.2 y
    ((tensorColimitRep_spec hc (a • b)).trans hy.symm) m
  have ht : y ⊗ₜ[A] m = r.2 ⊗ₜ[A] (a • m) := by
    change (a • r.2) ⊗ₜ[A] m = r.2 ⊗ₜ[A] (a • m)
    exact TensorProduct.smul_tmul a r.2 m
  change ConcreteCategory.hom (s.ι.app r'.1) (r'.2 ⊗ₜ[A] m) = _
  rw [heq, ht]
  rfl

private noncomputable def isColimit_moduleExtensionAddGroupCocone {A : Type u} [CommRing A]
    {I : Type i} [Category.{j} I] [IsFiltered I]
    [UnivLE.{i, max u v}] [UnivLE.{j, max u v}] {D : I ⥤ CommAlgCat.{max u v} A}
    {c : Cocone D} (hc : IsColimit c) (M : ModuleCat.{max u v w} A)
    :
    IsColimit (moduleExtensionAddGroupCocone c M) := by
  let s := moduleExtensionAddGroupCocone c M
  refine {
    desc := fun s' => AddCommGrpCat.ofHom (TensorProduct.liftAddHom
      (tensorCoconeBilinearMap hc M s') (tensorCoconeBilinearMap_balance hc M s'))
    fac := ?_
    uniq := ?_ }
  · intro s' k
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul b m =>
      let p := tensorCoconeBilinearMap hc M s'
      let hb := tensorCoconeBilinearMap_balance hc M s'
      change p ((c.ι.app k).hom b) m = ConcreteCategory.hom (s'.ι.app k) (b ⊗ₜ[A] m)
      let r := tensorColimitRep hc ((c.ι.app k).hom b)
      have heq := tensorCocone_rep_eq hc M s' r.2 b
        (tensorColimitRep_spec hc ((c.ι.app k).hom b)) m
      change ConcreteCategory.hom (s'.ι.app r.1) (r.2 ⊗ₜ[A] m) = _
      exact heq
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  · intro s' q hm
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul b n =>
      let p := tensorCoconeBilinearMap hc M s'
      let r := tensorColimitRep hc b
      have hh := ConcreteCategory.congr_hom (hm r.1) (r.2 ⊗ₜ[A] n)
      change (q.hom (b ⊗ₜ[A] n)) = (s'.ι.app r.1).hom (r.2 ⊗ₜ[A] n)
      have hs : (s.ι.app r.1).hom (r.2 ⊗ₜ[A] n) = b ⊗ₜ[A] n := by
        change (c.ι.app r.1).hom r.2 ⊗ₜ[A] n = _
        rw [tensorColimitRep_spec hc b]
      rw [← hs]
      exact hh
    | add x y hx hy =>
      calc
        q.hom (x + y) = q.hom x + q.hom y := map_add q.hom x y
        _ = (AddCommGrpCat.ofHom (TensorProduct.liftAddHom
            (tensorCoconeBilinearMap hc M s')
            (tensorCoconeBilinearMap_balance hc M s'))).hom x +
              (AddCommGrpCat.ofHom (TensorProduct.liftAddHom
                (tensorCoconeBilinearMap hc M s')
                (tensorCoconeBilinearMap_balance hc M s'))).hom y :=
          congrArg₂ (· + ·) hx hy
        _ = (AddCommGrpCat.ofHom (TensorProduct.liftAddHom
            (tensorCoconeBilinearMap hc M s')
            (tensorCoconeBilinearMap_balance hc M s'))).hom (x + y) :=
          (map_add _ x y).symm

private noncomputable def adequateKernelEmbedding {A : Type u} [CommRing A]
    (F : AdequateFunctor.ModuleValuedFunctor.{w, v} A)
    {M N : ModuleCat.{max u v w} A} (f : M ⟶ N)
    (e :
      (AdequateFunctor.presheafOfModulesUliftFunctor.{max u v}
      (AdequateFunctor.algebraRingDiagram A)).obj F ≅
      kernel ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map f))
    (X : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ) :
    F.obj X →+ TensorProduct A (X.unop.unop : Type max u v) (M : Type max u v w) :=
  let k := (kernel.ι ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map f)).app X
  let eX := e.hom.app X
  (k.hom.toAddMonoidHom).comp
    ((eX.hom.toAddMonoidHom).comp (AddEquiv.ulift.symm.toAddMonoidHom))

private theorem adequateKernelEmbedding_naturality {A : Type u} [CommRing A]
    (F : AdequateFunctor.ModuleValuedFunctor.{w, v} A)
    {M N : ModuleCat.{max u v w} A} (f : M ⟶ N)
    (e :
      (AdequateFunctor.presheafOfModulesUliftFunctor.{max u v}
      (AdequateFunctor.algebraRingDiagram A)).obj F ≅
      kernel ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map f))
    {X Y : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ} (a : X ⟶ Y) (x : F.obj X) :
    (moduleExtensionAddGroupFunctor M).map ((unopUnop (CommAlgCat.{max u v} A)).map a)
        (adequateKernelEmbedding F f e X x) =
      adequateKernelEmbedding F f e Y (F.presheaf.map a x) := by
  let g := (AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map f
  let UF := (AdequateFunctor.presheafOfModulesUliftFunctor.{max u v}
    (AdequateFunctor.algebraRingDiagram A)).obj F
  have hι := PresheafOfModules.naturality_apply (kernel.ι g) a
    ((e.hom.app X).hom (ULift.up.{max u v, w} x))
  have he := PresheafOfModules.naturality_apply e.hom a (ULift.up.{max u v, w} x)
  dsimp [adequateKernelEmbedding]
  change (moduleExtensionAddGroupFunctor M).map ((unopUnop (CommAlgCat.{max u v} A)).map a)
      (((kernel.ι g).app X).hom ((e.hom.app X).hom (ULift.up.{max u v, w} x))) =
    ((kernel.ι g).app Y).hom ((e.hom.app Y).hom (UF.map a (ULift.up.{max u v, w} x)))
  rw [he]
  exact hι.symm

/-- A section-wise kernel element of a morphism of presheaves of modules lifts to the kernel
presheaf. -/
private theorem exists_kernel_ι_app_eq {C : Type i} [Category.{j} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {P Q : PresheafOfModules.{w} R} (g : P ⟶ Q) (X : Cᵒᵖ) (z : P.obj X)
    (hz : (g.app X).hom z = 0) : ∃ x : (kernel g).obj X, ((kernel.ι g).app X).hom x = z := by
  let ev := PresheafOfModules.evaluation R X
  refine ⟨(PreservesKernel.iso ev g).inv.hom ((ModuleCat.kernelIsoKer (g.app X)).inv.hom
    ⟨z, LinearMap.mem_ker.mpr hz⟩), ?_⟩
  have hEval := ConcreteCategory.congr_hom (PreservesKernel.iso_inv_ι ev g)
    ((ModuleCat.kernelIsoKer (g.app X)).inv.hom ⟨z, LinearMap.mem_ker.mpr hz⟩)
  refine hEval.trans ?_
  change ((ModuleCat.kernelIsoKer (g.app X)).inv ≫ kernel.ι (g.app X)).hom
      ⟨z, LinearMap.mem_ker.mpr hz⟩ = z
  rw [ModuleCat.kernelIsoKer_inv_kernel_ι]
  rfl

private theorem adequateKernelEmbedding_injective {A : Type u} [CommRing A]
    (F : AdequateFunctor.ModuleValuedFunctor.{w, v} A)
    {M N : ModuleCat.{max u v w} A} (f : M ⟶ N)
    (e : (AdequateFunctor.presheafOfModulesUliftFunctor.{max u v}
      (AdequateFunctor.algebraRingDiagram A)).obj F ≅
        kernel ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map f))
    (X : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ) :
    Function.Injective (adequateKernelEmbedding F f e X) := by
  let g := (AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map f
  let ev := PresheafOfModules.evaluation (AdequateFunctor.algebraRingDiagram A) X
  let κ : (kernel g).obj X ≅ kernel (g.app X) := PreservesKernel.iso ev g
  have hκ : κ.hom ≫ kernel.ι (g.app X) = (kernel.ι g).app X := by
    change (PreservesKernel.iso ev g).hom ≫ kernel.ι (g.app X) = (kernel.ι g).app X
    rw [PreservesKernel.iso_hom]
    exact kernelComparison_comp_ι g ev
  have hK : Function.Injective ((kernel.ι g).app X).hom := by
    intro a b hab
    have ha : (kernel.ι (g.app X)).hom (κ.hom.hom a) =
        ((kernel.ι g).app X).hom a := by
      simpa using ConcreteCategory.congr_hom hκ a
    have hb : (kernel.ι (g.app X)).hom (κ.hom.hom b) =
        ((kernel.ι g).app X).hom b := by
      simpa using ConcreteCategory.congr_hom hκ b
    have hpoint : (kernel.ι (g.app X)).hom (κ.hom.hom a) =
        (kernel.ι (g.app X)).hom (κ.hom.hom b) := ha.trans (hab.trans hb.symm)
    have hk : Function.Injective κ.hom.hom := by
      intro x y hxy
      have hh := congrArg κ.inv.hom hxy
      simpa using hh
    exact hk ((ModuleCat.mono_iff_injective _).1 inferInstance hpoint)
  intro x y h
  change ((kernel.ι g).app X).hom ((e.hom.app X).hom (ULift.up x)) =
    ((kernel.ι g).app X).hom ((e.hom.app X).hom (ULift.up y)) at h
  have he : Function.Injective (e.hom.app X).hom := by
    intro a b hab
    have h' := congrArg (e.inv.app X).hom hab
    have hcomp : e.hom.app X ≫ e.inv.app X = 𝟙 _ := by
      have hh := congrArg (fun q => q.app X) e.hom_inv_id
      change e.hom.app X ≫ e.inv.app X = 𝟙 _ at hh
      exact hh
    have ha := ConcreteCategory.congr_hom hcomp a
    have hb := ConcreteCategory.congr_hom hcomp b
    exact ha.symm.trans (h'.trans hb)
  exact ULift.up_injective (he (hK h))

private theorem adequate_exists_stage_preimage {A : Type u} [CommRing A]
    (F : AdequateFunctor.ModuleValuedFunctor.{w, v} A)
    {I : Type i} [Category.{j} I] [IsFiltered I]
    [UnivLE.{i, max u v}] [UnivLE.{j, max u v}]
    (D : I ⥤ ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ) {c : Cocone D} (hc : IsColimit c)
    {M N : ModuleCat.{max u v w} A} (f : M ⟶ N)
    (e : (AdequateFunctor.presheafOfModulesUliftFunctor.{max u v}
      (AdequateFunctor.algebraRingDiagram A)).obj F ≅
        kernel ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map f))
    (x : F.obj c.pt) :
    ∃ (k : I) (y : F.obj (D.obj k)), F.presheaf.map (c.ι.app k) y = x := by
  classical
  let U := unopUnop (CommAlgCat.{max u v} A)
  let D₀ := D ⋙ U
  let c₀ := U.mapCocone c
  have hc₀ : IsColimit c₀ := isColimitOfPreserves U hc
  let tM := moduleExtensionAddGroupCocone c₀ M
  let tN := moduleExtensionAddGroupCocone c₀ N
  have htM := isColimit_moduleExtensionAddGroupCocone hc₀ M
  have htN := isColimit_moduleExtensionAddGroupCocone hc₀ N
  let z := adequateKernelEmbedding F f e c.pt x
  let GM := D₀ ⋙ moduleExtensionAddGroupFunctor M
  let GN := D₀ ⋙ moduleExtensionAddGroupFunctor N
  let L := AddCommGrpCat.uliftFunctor.{max i j u v w, max u v w}
  have : PreservesFilteredColimitsOfSize.{j, i}
      (forget AddCommGrpCat.{max i j u v w}) :=
    preservesFilteredColimitsOfSize_shrink.{i, max i j u v w, j, max i j u v w}
      (forget AddCommGrpCat.{max i j u v w})
  have : PreservesColimitsOfShape I (forget AddCommGrpCat.{max i j u v w}) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits I
  let tM' := L.mapCocone tM
  let tN' := L.mapCocone tN
  have htM' : IsColimit tM' := isColimitOfPreserves L htM
  have htN' : IsColimit tN' := isColimitOfPreserves L htN
  obtain ⟨i, zi', hzi'⟩ := Concrete.isColimit_exists_rep (GM ⋙ L) htM'
    (ULift.up.{max i j u v w, max u v w} z)
  let zi : GM.obj i := zi'.down
  have hzi : (tM.ι.app i).hom zi = z := by
    change ULift.up ((tM.ι.app i).hom zi) = ULift.up z at hzi'
    exact congrArg ULift.down hzi'
  let g := (AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map f
  have hz : (((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map f).app c.pt).hom z = 0
    := by
    have hcond : (kernel.ι g).app c.pt ≫ g.app c.pt = 0 := by
      have hh := congrArg (fun q => q.app c.pt) (kernel.condition g)
      change (kernel.ι g).app c.pt ≫ g.app c.pt = 0 at hh
      exact hh
    change (g.app c.pt).hom
      (((kernel.ι g).app c.pt).hom ((e.hom.app c.pt).hom (ULift.up x))) = 0
    have h := ConcreteCategory.congr_hom hcond ((e.hom.app c.pt).hom (ULift.up x))
    simpa using h
  have hstageKernel : ∃ (k : I) (zk : TensorProduct A (D₀.obj k : Type max u v)
      (M : Type max u v w)),
      (((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map f).app (D.obj k)).hom zk = 0 ∧
        (tM.ι.app k).hom zk = z := by
    have hcomm : (tN.ι.app i).hom ((g.app (D.obj i)).hom zi) =
        (g.app c.pt).hom ((tM.ι.app i).hom zi) := by
      induction zi using TensorProduct.inductionOn with
      | tmul b m => rfl
      | add x y hx hy =>
        simp only [map_add, hx, hy]
        exact (map_add (g.app c.pt).hom _ _).symm
    have hzero : (tN.ι.app i).hom ((g.app (D.obj i)).hom zi) =
        (tN.ι.app i).hom 0 := by
      rw [hcomm, hzi, hz]
      change 0 = (tN.ι.app i).hom (0 : GN.obj i)
      rw [map_zero]
    obtain ⟨k, α, β, hαβ⟩ := Concrete.isColimit_exists_of_rep_eq
      (GN ⋙ L) htN' (ULift.up ((g.app (D.obj i)).hom zi)) (ULift.up (0 : GN.obj i)) (by
        change ULift.up ((tN.ι.app i).hom ((g.app (D.obj i)).hom zi)) =
          ULift.up ((tN.ι.app i).hom (0 : GN.obj i))
        exact congrArg ULift.up hzero)
    let zk : GM.obj k := (GM.map α) zi
    have hkernel : (g.app (D.obj k)).hom zk = 0 := by
      have hαβ' : (GN.map α) ((g.app (D.obj i)).hom zi) = 0 := by
        have hdown := congrArg ULift.down hαβ
        change (GN.map α).hom ((g.app (D.obj i)).hom zi) = (GN.map β).hom 0 at hdown
        simpa using hdown
      have hnat' := PresheafOfModules.naturality_apply g (D.map α) zi
      change (g.app (D.obj k)).hom ((GM.map α) zi) =
        (GN.map α) ((g.app (D.obj i)).hom zi) at hnat'
      calc
        (g.app (D.obj k)).hom zk = (g.app (D.obj k)).hom ((GM.map α) zi) := rfl
        _ = (GN.map α) ((g.app (D.obj i)).hom zi) := hnat'
        _ = 0 := hαβ'
    have hstage : (tM.ι.app k).hom zk = z := by
      change (tM.ι.app k).hom ((GM.map α).hom zi) = z
      have hh := ConcreteCategory.congr_hom (tM.w α) zi
      change (tM.ι.app k).hom ((GM.map α).hom zi) = (tM.ι.app i).hom zi at hh
      exact hh.trans hzi
    exact ⟨k, zk, hkernel, hstage⟩
  obtain ⟨k, zk, hzk, hzkc⟩ := hstageKernel
  let X := D.obj k
  obtain ⟨kx, hkx⟩ := exists_kernel_ι_app_eq g X zk hzk
  let yULift := (e.inv.app X).hom kx
  let y : F.obj (D.obj k) := yULift.down
  have hyemb : adequateKernelEmbedding F f e (D.obj k) y = zk := by
    have he : (e.hom.app X).hom yULift = kx := by
      have hcomp : e.inv.app X ≫ e.hom.app X = 𝟙 _ := by
        have hh := congrArg (fun q => q.app X) e.inv_hom_id
        change e.inv.app X ≫ e.hom.app X = 𝟙 _ at hh
        exact hh
      have hh := ConcreteCategory.congr_hom hcomp kx
      change (e.hom.app X).hom ((e.inv.app X).hom kx) = kx at hh
      exact hh
    change ((kernel.ι g).app X).hom ((e.hom.app X).hom yULift) = zk
    rw [he]
    exact hkx
  have htransport : adequateKernelEmbedding F f e c.pt
      (F.presheaf.map (c.ι.app k) y) = z := by
    let yP : (F.presheaf.obj (D.obj k) : Type _) := y
    change adequateKernelEmbedding F f e c.pt (F.presheaf.map (c.ι.app k) yP) = z
    have hnat := adequateKernelEmbedding_naturality F f e (c.ι.app k) yP
    have hnat' : (moduleExtensionAddGroupFunctor M).map
        ((unopUnop (CommAlgCat.{max u v} A)).map (c.ι.app k))
        (adequateKernelEmbedding F f e (D.obj k) yP) =
        adequateKernelEmbedding F f e c.pt (F.presheaf.map (c.ι.app k) yP) := by
      simpa using hnat
    have hι : (moduleExtensionAddGroupFunctor M).map
        ((unopUnop (CommAlgCat.{max u v} A)).map (c.ι.app k)) = tM.ι.app k := rfl
    have hstep : (moduleExtensionAddGroupFunctor M).map
        ((unopUnop (CommAlgCat.{max u v} A)).map (c.ι.app k))
        (adequateKernelEmbedding F f e (D.obj k) yP) = (tM.ι.app k).hom zk := by
      rw [hι]
      exact congrArg (tM.ι.app k).hom hyemb
    exact hnat'.symm.trans (hstep.trans hzkc)
  refine ⟨k, y, adequateKernelEmbedding_injective F f e c.pt ?_⟩
  simpa [z] using htransport

private theorem adequate_exists_stage_eq {A : Type u} [CommRing A]
    (F : AdequateFunctor.ModuleValuedFunctor.{w, v} A)
    {I : Type i} [Category.{j} I] [IsFiltered I]
    [UnivLE.{i, max u v}] [UnivLE.{j, max u v}]
    {D : I ⥤ ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ} {c : Cocone D} (hc : IsColimit c)
    {M N : ModuleCat.{max u v w} A} (f : M ⟶ N)
    (e : (AdequateFunctor.presheafOfModulesUliftFunctor.{max u v}
      (AdequateFunctor.algebraRingDiagram A)).obj F ≅
        kernel ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map f))
    {i j : I} (x : F.obj (D.obj i)) (y : F.obj (D.obj j))
    (hxy : F.presheaf.map (c.ι.app i) x = F.presheaf.map (c.ι.app j) y) :
    ∃ (k : I) (a : i ⟶ k) (b : j ⟶ k),
      F.presheaf.map (D.map a) x = F.presheaf.map (D.map b) y := by
  let U := unopUnop (CommAlgCat.{max u v} A)
  let D₀ := D ⋙ U
  let c₀ := U.mapCocone c
  have hc₀ : IsColimit c₀ := isColimitOfPreserves U hc
  let tM := moduleExtensionAddGroupCocone c₀ M
  have htM := isColimit_moduleExtensionAddGroupCocone hc₀ M
  let GM := D₀ ⋙ moduleExtensionAddGroupFunctor M
  let L := AddCommGrpCat.uliftFunctor.{max i j u v w, max u v w}
  have : PreservesFilteredColimitsOfSize.{j, i}
      (forget AddCommGrpCat.{max i j u v w}) :=
    preservesFilteredColimitsOfSize_shrink.{i, max i j u v w, j, max i j u v w}
      (forget AddCommGrpCat.{max i j u v w})
  have : PreservesColimitsOfShape I (forget AddCommGrpCat.{max i j u v w}) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits I
  let tM' := L.mapCocone tM
  have htM' : IsColimit tM' := isColimitOfPreserves L htM
  let z₁ := adequateKernelEmbedding F f e (D.obj i) x
  let z₂ := adequateKernelEmbedding F f e (D.obj j) y
  have hz₁ : (tM.ι.app i).hom z₁ =
      adequateKernelEmbedding F f e c.pt (F.presheaf.map (c.ι.app i) x) :=
    adequateKernelEmbedding_naturality F f e (c.ι.app i) x
  have hz₂ : (tM.ι.app j).hom z₂ =
      adequateKernelEmbedding F f e c.pt (F.presheaf.map (c.ι.app j) y) :=
    adequateKernelEmbedding_naturality F f e (c.ι.app j) y
  have hglobal : (tM.ι.app i).hom z₁ = (tM.ι.app j).hom z₂ := by
    rw [hz₁, hz₂, hxy]
  obtain ⟨k, a, b, hab⟩ := Concrete.isColimit_exists_of_rep_eq
    (GM ⋙ L) htM' (ULift.up z₁) (ULift.up z₂) (congrArg ULift.up hglobal)
  have hma : (GM.map a).hom z₁ =
      adequateKernelEmbedding F f e (D.obj k) (F.presheaf.map (D.map a) x) :=
    adequateKernelEmbedding_naturality F f e (D.map a) x
  have hmb : (GM.map b).hom z₂ =
      adequateKernelEmbedding F f e (D.obj k) (F.presheaf.map (D.map b) y) :=
    adequateKernelEmbedding_naturality F f e (D.map b) y
  have hstage :
      adequateKernelEmbedding F f e (D.obj k) (F.presheaf.map (D.map a) x) =
        adequateKernelEmbedding F f e (D.obj k) (F.presheaf.map (D.map b) y) := by
    have hma' : (GM ⋙ L).map a (ULift.up z₁) = ULift.up
        (adequateKernelEmbedding F f e (D.obj k) (F.presheaf.map (D.map a) x)) := by
      change ULift.up ((GM.map a).hom z₁) = _
      exact congrArg ULift.up hma
    have hmb' : (GM ⋙ L).map b (ULift.up z₂) = ULift.up
        (adequateKernelEmbedding F f e (D.obj k) (F.presheaf.map (D.map b) y)) := by
      change ULift.up ((GM.map b).hom z₂) = _
      exact congrArg ULift.up hmb
    exact ULift.up_injective (hma'.symm.trans (hab.trans hmb'))
  exact ⟨k, a, b, adequateKernelEmbedding_injective F f e (D.obj k) hstage⟩

/-- An adequate functor sends filtered colimits of commutative algebras to colimits of
its underlying additive groups. -/
@[stacks 06UU]
public theorem isColimit_mapCocone_of_isAdequate
    {A : Type u} [CommRing A] (F : AdequateFunctor.ModuleValuedFunctor.{w, v} A)
    (hF : AdequateFunctor.IsAdequate (𝟭 _) F)
    {I : Type i} [Category.{j} I] [IsFiltered I]
    [UnivLE.{i, max u v}] [UnivLE.{j, max u v}]
    {D : I ⥤ ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ}
    {c : Cocone D} (hc : IsColimit c) :
    Nonempty (IsColimit (F.presheaf.mapCocone c)) := by
  classical
  rcases hF with ⟨M, N, f, hF⟩
  rcases hF with ⟨e⟩
  let d := F.presheaf.mapCocone c
  let rep (x : F.obj c.pt) : Σ k : I, F.obj (D.obj k) := by
    let h := adequate_exists_stage_preimage F D hc f e x
    exact ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩
  have rep_spec (x : F.obj c.pt) :
      F.presheaf.map (c.ι.app (rep x).1) (rep x).2 = x :=
    Classical.choose_spec (Classical.choose_spec
      (adequate_exists_stage_preimage F D hc f e x))
  have cocone_map_eq (s : Cocone (D ⋙ F.presheaf)) {i j : I}
      {x : F.obj (D.obj i)} {y : F.obj (D.obj j)}
      (h : F.presheaf.map (c.ι.app i) x = F.presheaf.map (c.ι.app j) y) :
      (s.ι.app i).hom x = (s.ι.app j).hom y := by
    obtain ⟨k, a, b, hab⟩ := adequate_exists_stage_eq F hc f e x y h
    calc
      (s.ι.app i).hom x = (s.ι.app k).hom (F.presheaf.map (D.map a) x) :=
        (ConcreteCategory.congr_hom (s.w a) x).symm
      _ = (s.ι.app k).hom (F.presheaf.map (D.map b) y) := congrArg _ hab
      _ = (s.ι.app j).hom y := ConcreteCategory.congr_hom (s.w b) y
  let descHom (s : Cocone (D ⋙ F.presheaf)) : F.obj c.pt →+ s.pt := {
    toFun := fun x => (s.ι.app (rep x).1).hom (rep x).2
    map_zero' := by
      let r := rep (0 : F.obj c.pt)
      let k : I := IsFiltered.nonempty.some
      have hr : F.presheaf.map (c.ι.app r.1) r.2 =
          F.presheaf.map (c.ι.app k) (0 : F.obj (D.obj k)) := by
        calc
          F.presheaf.map (c.ι.app r.1) r.2 = 0 := rep_spec 0
          _ = F.presheaf.map (c.ι.app k) 0 := (map_zero _).symm
      change (s.ι.app r.1).hom r.2 = 0
      exact (cocone_map_eq s hr).trans (map_zero (s.ι.app k).hom)
    map_add' x y := by
      let rx := rep x
      let ry := rep y
      let k := IsFiltered.max rx.1 ry.1
      let a := IsFiltered.leftToMax rx.1 ry.1
      let b := IsFiltered.rightToMax rx.1 ry.1
      let z := F.presheaf.map (D.map a) rx.2 + F.presheaf.map (D.map b) ry.2
      have hca : F.presheaf.map (D.map a) ≫ F.presheaf.map (c.ι.app k) =
          F.presheaf.map (c.ι.app rx.1) := by
        rw [← Functor.map_comp, c.w a]
      have hcb : F.presheaf.map (D.map b) ≫ F.presheaf.map (c.ι.app k) =
          F.presheaf.map (c.ι.app ry.1) := by
        rw [← Functor.map_comp, c.w b]
      have hxa : F.presheaf.map (c.ι.app k) (F.presheaf.map (D.map a) rx.2) = x :=
        (ConcreteCategory.congr_hom hca rx.2).trans (rep_spec x)
      have hyb : F.presheaf.map (c.ι.app k) (F.presheaf.map (D.map b) ry.2) = y :=
        (ConcreteCategory.congr_hom hcb ry.2).trans (rep_spec y)
      have hz : F.presheaf.map (c.ι.app k) z = x + y := by
        change F.presheaf.map (c.ι.app k)
            (F.presheaf.map (D.map a) rx.2 + F.presheaf.map (D.map b) ry.2) = _
        rw [map_add, hxa, hyb]
        rfl
      have hrep := cocone_map_eq s (i := (rep (x + y)).1) (j := k)
        (x := (rep (x + y)).2) (y := z) ((rep_spec (x + y)).trans hz.symm)
      change (s.ι.app (rep (x + y)).1).hom (rep (x + y)).2 = _
      rw [hrep]
      change (s.ι.app k).hom z = _
      change (s.ι.app k).hom
          (F.presheaf.map (D.map a) rx.2 + F.presheaf.map (D.map b) ry.2) = _
      rw [map_add]
      have h₁ := ConcreteCategory.congr_hom (s.w a) rx.2
      have h₂ := ConcreteCategory.congr_hom (s.w b) ry.2
      change (s.ι.app k).hom (F.presheaf.map (D.map a) rx.2) =
          (s.ι.app rx.1).hom rx.2 at h₁
      change (s.ι.app k).hom (F.presheaf.map (D.map b) ry.2) =
          (s.ι.app ry.1).hom ry.2 at h₂
      rw [h₁, h₂]
  }
  refine ⟨{
    desc := fun s => AddCommGrpCat.ofHom (descHom s)
    fac := ?_
    uniq := ?_ }⟩
  · intro s i
    ext x
    have hh := cocone_map_eq s (rep_spec (F.presheaf.map (c.ι.app i) x))
    change (s.ι.app (rep (F.presheaf.map (c.ι.app i) x)).1).hom
        (rep (F.presheaf.map (c.ι.app i) x)).2 = (s.ι.app i).hom x
    exact hh
  · intro s m hm
    ext x
    let r := rep x
    have hh := ConcreteCategory.congr_hom (hm r.1) r.2
    change m.hom x = (s.ι.app r.1).hom r.2
    rw [← rep_spec x]
    exact hh

end

section

open CategoryTheory CategoryTheory.Limits

universe u v w s


open TensorProduct

private structure FiniteKernelDiagram
    {A : Type u} [CommRing A] [Small.{s} A]
    (M N : ModuleCat.{s} A) (φ : M ⟶ N) : Type s where
  n : ℕ
  m : ℕ
  q : Fin n → Fin m → Shrink.{s} A
  g : Fin n → M
  h : Fin m → N
  comm : ∀ i, φ.hom (g i) = ∑ j, (equivShrink A).symm (q i j) • h j

private noncomputable def diagramQLinear
    {A : Type u} [CommRing A] [Small.{s} A] (M N : ModuleCat.{s} A)
    (φ : M ⟶ N) (d : FiniteKernelDiagram.{u, s} M N φ) :
    (Fin d.n → A) →ₗ[A] (Fin d.m → A) :=
  (Pi.basisFun A (Fin d.n)).constr A (fun i j =>
    (equivShrink A).symm (d.q i j))

private noncomputable def diagramGLinear
    {A : Type u} [CommRing A] [Small.{s} A] (M N : ModuleCat.{s} A)
    (φ : M ⟶ N) (d : FiniteKernelDiagram.{u, s} M N φ) :
    (Fin d.n → A) →ₗ[A] M :=
  (Pi.basisFun A (Fin d.n)).constr A d.g

private noncomputable def diagramHLinear
    {A : Type u} [CommRing A] [Small.{s} A] (M N : ModuleCat.{s} A)
    (φ : M ⟶ N) (d : FiniteKernelDiagram.{u, s} M N φ) :
    (Fin d.m → A) →ₗ[A] N :=
  (Pi.basisFun A (Fin d.m)).constr A d.h

set_option linter.checkUnivs false in
private noncomputable def liftFreeMap
    {A : Type u} [CommRing A] (n m : ℕ)
    (f : (Fin n → A) →ₗ[A] (Fin m → A)) :
  AdequateFunctor.finiteFreeModule.{max u v w} A n ⟶
      AdequateFunctor.finiteFreeModule.{max u v w} A m :=
  (ModuleCat.uliftFunctor.{max u v w, u} A).map (ModuleCat.ofHom f)

set_option linter.checkUnivs false in
private noncomputable def liftFreeToModule
    {A : Type u} [CommRing A] {M : ModuleCat.{max u v w} A} (n : ℕ)
    (f : (Fin n → A) →ₗ[A] M) :
    AdequateFunctor.finiteFreeModule.{max u v w} A n ⟶ M :=
  ModuleCat.ofHom (f.comp ULift.moduleEquiv.toLinearMap)

private noncomputable def diagramQ
    {A : Type u} [CommRing A] [Small.{max u v w} A] {M N : ModuleCat.{max u v w} A}
    {φ : M ⟶ N} (d : FiniteKernelDiagram.{u, max u v w} M N φ) :
    (AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).obj
      (AdequateFunctor.finiteFreeModule.{max u v w} A d.n) ⟶
        (AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).obj
          (AdequateFunctor.finiteFreeModule.{max u v w} A d.m) :=
  (AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map
    (liftFreeMap.{u, v, w} (A := A) d.n d.m
      (diagramQLinear.{u, max u v w} M N φ d))

private noncomputable def diagramG
    {A : Type u} [CommRing A] [Small.{max u v w} A] {M N : ModuleCat.{max u v w} A}
    {φ : M ⟶ N} (d : FiniteKernelDiagram.{u, max u v w} M N φ) :
    (AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).obj
      (AdequateFunctor.finiteFreeModule.{max u v w} A d.n) ⟶
        (AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).obj M :=
  (AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map
    (liftFreeToModule.{u, v, w} (A := A) d.n
      (diagramGLinear.{u, max u v w} M N φ d))

private noncomputable def diagramH
    {A : Type u} [CommRing A] [Small.{max u v w} A] {M N : ModuleCat.{max u v w} A}
    {φ : M ⟶ N} (d : FiniteKernelDiagram.{u, max u v w} M N φ) :
    (AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).obj
      (AdequateFunctor.finiteFreeModule.{max u v w} A d.m) ⟶
        (AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).obj N :=
  (AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map
    (liftFreeToModule.{u, v, w} (A := A) d.m
      (diagramHLinear.{u, max u v w} M N φ d))

private noncomputable def finiteKernelDiagramMap
    {A : Type u} [CommRing A] [Small.{max u v w} A] {M N : ModuleCat.{max u v w} A}
    {φ : M ⟶ N} (F : AdequateFunctor.ModuleValuedFunctor.{w, v} A)
    (e : (AdequateFunctor.presheafOfModulesUliftFunctor.{max u v, w}
      (AdequateFunctor.algebraRingDiagram.{v} A)).obj F ≅
        kernel ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map φ))
    (d : FiniteKernelDiagram.{u, max u v w} M N φ) :
    kernel (diagramQ.{u, v, w} d) ⟶
      (AdequateFunctor.presheafOfModulesUliftFunctor.{max u v, w}
        (AdequateFunctor.algebraRingDiagram.{v} A)).obj F := by
  let φ' := (AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map φ
  have hlin : φ.hom.comp (diagramGLinear.{u, max u v w} M N φ d) =
      (diagramHLinear.{u, max u v w} M N φ d).comp
        (diagramQLinear.{u, max u v w} M N φ d) := by
    ext i
    simp [diagramQLinear, diagramGLinear, diagramHLinear, d.comm]
  have hraw :
      liftFreeMap.{u, v, w} (A := A) d.n d.m
          (diagramQLinear.{u, max u v w} M N φ d) ≫
        liftFreeToModule.{u, v, w} (A := A) d.m
          (diagramHLinear.{u, max u v w} M N φ d) =
      liftFreeToModule.{u, v, w} (A := A) d.n
        (diagramGLinear.{u, max u v w} M N φ d) ≫ φ := by
    ext p
    let down : ULift.{max u v w} (Fin d.n → A) ≃ₗ[A] (Fin d.n → A) :=
      ULift.moduleEquiv
    change diagramHLinear.{u, max u v w} M N φ d
        (diagramQLinear.{u, max u v w} M N φ d (down p)) =
      φ.hom (diagramGLinear.{u, max u v w} M N φ d (down p))
    exact LinearMap.congr_fun hlin.symm (down p)
  have hcomm : diagramQ.{u, v, w} d ≫ diagramH.{u, v, w} d =
      diagramG.{u, v, w} d ≫ φ' := by
    dsimp [diagramQ, diagramG, diagramH, φ']
    rw [← Functor.map_comp, ← Functor.map_comp, hraw]
  let a : kernel (diagramQ.{u, v, w} d) ⟶ kernel φ' :=
    kernel.lift φ' (kernel.ι (diagramQ.{u, v, w} d) ≫ diagramG.{u, v, w} d) (by
      rw [Category.assoc, ← hcomm, ← Category.assoc, kernel.condition, zero_comp])
  exact a ≫ e.inv

private lemma exists_diagram_tensor_preimage
    {A : Type u} [CommRing A] [Small.{max u v w} A] {M N : ModuleCat.{max u v w} A}
    {φ : M ⟶ N} (F : AdequateFunctor.ModuleValuedFunctor.{w, v} A)
    (e : (AdequateFunctor.presheafOfModulesUliftFunctor.{max u v, w}
      (AdequateFunctor.algebraRingDiagram.{v} A)).obj F ≅
        kernel ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map φ))
    (X : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ)
      (y : ((AdequateFunctor.presheafOfModulesUliftFunctor.{max u v, w}
      (AdequateFunctor.algebraRingDiagram.{v} A)).obj F).obj X) :
    ∃ d : FiniteKernelDiagram.{u, max u v w} M N φ,
      ∃ z : ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).obj
        (AdequateFunctor.finiteFreeModule.{max u v w} A d.n)).obj X,
        (diagramQ.{u, v, w} d).app X z = 0 ∧
          (diagramG.{u, v, w} d).app X z = (kernel.ι
            ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map φ)).app X
              (e.hom.app X y) := by
  classical
  let B : Type (max u v) := X.unop.unop
  let : CommRing B := inferInstance
  let : Algebra A B := inferInstance
  let w₀ : B ⊗[A] M := (kernel.ι
    ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map φ)).app X (e.hom.app X y)
  obtain ⟨r, b, m, hw⟩ := TensorProduct.exists_sum_tmul_eq w₀
  let x : M ⊗[A] B := ∑ i, m i ⊗ₜ[A] b i
  have hk := congrArg (fun f => f.app X)
      (kernel.condition ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map φ))
  have hk' := congrArg (fun f => f.hom (e.hom.app X y)) hk
  have hk'' : (((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map φ).app X) w₀ = 0 := by
    change ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map φ).app X
        ((kernel.ι ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map φ)).app X
          (e.hom.app X y)) = 0
    exact hk'
  let g₀ : (Fin r → A) →ₗ[A] M := (Pi.basisFun A (Fin r)).constr A m
  let x₀ : (Fin r → A) ⊗[A] B := ∑ i, (Pi.single i (1 : A)) ⊗ₜ[A] b i
  have hx₀ : g₀.rTensor B x₀ = x := by
    change g₀.rTensor B (∑ i, (Pi.single i (1 : A)) ⊗ₜ[A] b i) =
      ∑ i, m i ⊗ₜ[A] b i
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [LinearMap.rTensor_tmul]
    congr 1
    simpa [g₀, ← Pi.basisFun_apply] using
      (Pi.basisFun A (Fin r)).constr_basis A m i
  have hsum : ∑ i, b i ⊗ₜ[A] φ.hom (m i) = 0 := by
    rw [hw] at hk''
    have hterm (i : Fin r) :
        (ConcreteCategory.hom
          (((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map φ).app X))
            (b i ⊗ₜ[A] m i) = b i ⊗ₜ[A] φ.hom (m i) := by
      change (((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map φ).app X)
          (b i ⊗ₜ[A] m i) = _
      exact AdequateFunctor.moduleExtensionFunctor_map_app_tmul A φ X (b i) (m i)
    simpa only [map_sum, hterm] using hk''
  have hφx : φ.hom.rTensor B x = 0 := by
    apply (TensorProduct.comm A N B).injective
    simpa [x, map_sum, LinearMap.rTensor_tmul, TensorProduct.comm_tmul] using hsum
  let f₀ : (Fin r → A) →ₗ[A] N := φ.hom.comp g₀
  have hzero : f₀.rTensor B x₀ = 0 := by
    change (φ.hom.comp g₀).rTensor B x₀ = 0
    rw [LinearMap.rTensor_comp]
    change φ.hom.rTensor B (g₀.rTensor B x₀) = 0
    rw [hx₀]
    exact hφx
  let E : (Fin r → A) ≃ₗ[A] ULift.{max u v w} (Fin r → A) := ULift.moduleEquiv.symm
  let : Module.FinitePresentation A (ULift.{max u v w} (Fin r → A)) :=
    Module.FinitePresentation.of_equiv E
  let xLift : (ULift.{max u v w} (Fin r → A)) ⊗[A] B :=
    E.toLinearMap.rTensor B x₀
  let fLift : ULift.{max u v w} (Fin r → A) →ₗ[A] N :=
    φ.hom.comp (g₀.comp E.symm.toLinearMap)
  have hcancel : E.symm.toLinearMap.rTensor B xLift = x₀ := by
    change ((E.symm.toLinearMap.rTensor B).comp (E.toLinearMap.rTensor B)) x₀ = x₀
    rw [← LinearMap.rTensor_comp]
    simp [E]
  have hzeroLift : fLift.rTensor B xLift = 0 := by
    change (φ.hom.comp (g₀.comp E.symm.toLinearMap)).rTensor B
      (E.toLinearMap.rTensor B x₀) = 0
    rw [LinearMap.rTensor_comp, LinearMap.rTensor_comp]
    change φ.hom.rTensor B
      (g₀.rTensor B (E.symm.toLinearMap.rTensor B (E.toLinearMap.rTensor B x₀))) = 0
    rw [hcancel, hx₀]
    exact hφx
  obtain ⟨P, hPadd, hPmod, hPfp, f', β, hφ, hx⟩ :=
    LinearMap.exists_finitePresentation_factorization_of_rTensor_apply_eq_zero.{u, max u v w, max u
      v}
      (R := A) (P := ULift.{max u v w} (Fin r → A)) (Q := B) fLift hzeroLift
  let : AddCommGroup P := hPadd
  let : Module A P := hPmod
  let : Module.FinitePresentation A P := hPfp
  obtain ⟨k, l, p, ρ, hp, hExact⟩ := Module.FinitePresentation.exists_fin' A P
  obtain ⟨αLift, hαLift⟩ := Module.projective_lifting_property p f' hp
  let α : (Fin r → A) →ₗ[A] (Fin k → A) := αLift.comp E.toLinearMap
  have hα : p.comp α = f'.comp E.toLinearMap := by
    rw [← LinearMap.comp_assoc, hαLift]
  have hφ0 : f₀ = β.comp (f'.comp E.toLinearMap) := by
    have ht : fLift.comp E.toLinearMap = f₀ := by
      ext x
      simp [fLift, f₀, E]
    rw [← ht, hφ]
    rw [LinearMap.comp_assoc]
  have hrel : p.rTensor B (α.rTensor B x₀) = 0 := by
    change ((p.rTensor B).comp (α.rTensor B)) x₀ = 0
    rw [← LinearMap.rTensor_comp, hα, LinearMap.rTensor_comp]
    exact hx
  have hT := rTensor_exact B hExact hp
  rw [LinearMap.exact_iff] at hT
  have hmem : α.rTensor B x₀ ∈ LinearMap.range (ρ.rTensor B) := by
    rw [← hT]
    exact hrel
  obtain ⟨ct, hct⟩ := hmem
  obtain ⟨s, v₀, c, hc⟩ := TensorProduct.exists_sum_tmul_eq ct
  let cols : Fin (r + s) → (Fin k → A) := Fin.addCases
    (fun i => α (Pi.single i (1 : A))) (fun j => -ρ (v₀ j))
  let gm : Fin (r + s) → M := Fin.addCases m (fun _ => 0)
  let hm : Fin k → N := fun j => β (p (Pi.single j (1 : A)))
  let H : (Fin k → A) →ₗ[A] N := (Pi.basisFun A (Fin k)).constr A hm
  have hH : H = β.comp p := by
    apply (Pi.basisFun A (Fin k)).ext
    intro j
    change ((Pi.basisFun A (Fin k)).constr A hm) (Pi.basisFun A (Fin k) j) =
      β (p (Pi.basisFun A (Fin k) j))
    rw [(Pi.basisFun A (Fin k)).constr_basis]
    simp [hm, ← Pi.basisFun_apply]
  have hsumH (a : Fin k → A) : ∑ j, a j • hm j = β (p a) := by
    calc
      ∑ j, a j • hm j = H a := by
        simp [H, Module.Basis.constr_apply_fintype]
      _ = β (p a) := by
        simpa only [LinearMap.comp_apply] using congrArg (fun f => f a) hH
  have hTensor :
      (∑ i, b i ⊗ₜ[A] α (Pi.single i (1 : A))) =
        (∑ j, c j ⊗ₜ[A] ρ (v₀ j)) := by
    have hswap := congrArg (TensorProduct.comm A (Fin k → A) B) hct
    simpa [hc, x₀, map_sum, LinearMap.rTensor_tmul, TensorProduct.comm_tmul] using hswap.symm
  let d : FiniteKernelDiagram.{u, max u v w} M N φ := by
    refine ⟨r + s, k, fun i j => equivShrink A (cols i j), gm, hm, ?_⟩
    intro i
    have hsum_i :
        (∑ j, (equivShrink A).symm (equivShrink A (cols i j)) • hm j) =
          β (p (cols i)) := by simpa using hsumH (cols i)
    have hi := (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s)).apply_symm_apply i
    rcases h : (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s)).symm i with j | j
    · have hg : gm i = m j := by
        rw [← hi, h]
        simp [gm, finSumFinEquiv_apply_left]
      have hc : cols i = α (Pi.single j (1 : A)) := by
        rw [← hi, h]
        simp [cols, finSumFinEquiv_apply_left]
      have hαj : p (α (Pi.single j (1 : A))) = f' (E (Pi.single j (1 : A))) := by
        have := congrArg (fun f => f (Pi.single j (1 : A))) hα
        exact this
      have hφj : φ.hom (g₀ (Pi.single j (1 : A))) =
          β (f' (E (Pi.single j (1 : A)))) := by
        have := congrArg (fun f => f (Pi.single j (1 : A))) hφ0
        change φ.hom (g₀ (Pi.single j (1 : A))) = β (f' (E (Pi.single j (1 : A))))
        simpa [f₀, LinearMap.comp_apply] using this
      have hg₀j : g₀ (Pi.single j (1 : A)) = m j := by
        simpa [g₀, ← Pi.basisFun_apply] using (Pi.basisFun A (Fin r)).constr_basis A m j
      rw [hsum_i, hg, hc, hαj]
      simpa only [hg₀j] using hφj
    · have hg : gm i = 0 := by
        rw [← hi, h]
        simp [gm, finSumFinEquiv_apply_right]
      have hc : cols i = -ρ (v₀ j) := by
        rw [← hi, h]
        simp [cols, finSumFinEquiv_apply_right]
      have hρ : p (ρ (v₀ j)) = 0 := hExact.apply_apply_eq_zero _
      rw [hsum_i, hg, hc, map_neg, hρ]
      simp
  have hQL : diagramQLinear.{u, max u v w} M N φ d =
      (Pi.basisFun A (Fin (r + s))).constr A cols := by
    simp [diagramQLinear, d]
  have hGL : diagramGLinear.{u, max u v w} M N φ d =
      (Pi.basisFun A (Fin (r + s))).constr A gm := rfl
  have hQLleft (i : Fin r) :
      diagramQLinear.{u, max u v w} M N φ d (Pi.single (Fin.castAdd s i) (1 : A)) =
        α (Pi.single i (1 : A)) := by
    rw [hQL, ← Pi.basisFun_apply, (Pi.basisFun A (Fin (r + s))).constr_basis]
    simp [cols]
  have hQLright (j : Fin s) :
      diagramQLinear.{u, max u v w} M N φ d (Pi.single (Fin.natAdd r j) (1 : A)) =
        -ρ (v₀ j) := by
    rw [hQL, ← Pi.basisFun_apply, (Pi.basisFun A (Fin (r + s))).constr_basis]
    simp [cols]
  have hGLleft (i : Fin r) :
      diagramGLinear.{u, max u v w} M N φ d (Pi.single (Fin.castAdd s i) (1 : A)) = m i := by
    rw [hGL, ← Pi.basisFun_apply, (Pi.basisFun A (Fin (r + s))).constr_basis]
    simp [gm]
  have hGLright (j : Fin s) :
      diagramGLinear.{u, max u v w} M N φ d (Pi.single (Fin.natAdd r j) (1 : A)) = 0 := by
    rw [hGL, ← Pi.basisFun_apply, (Pi.basisFun A (Fin (r + s))).constr_basis]
    simp [gm]
  have hTensorUp :
      (∑ i, b i ⊗ₜ[A]
        (ULift.up (α (Pi.single i (1 : A))) :
          ↑(AdequateFunctor.finiteFreeModule.{max u v w} A k))) =
        ∑ j, c j ⊗ₜ[A]
          (ULift.up (ρ (v₀ j)) : ↑(AdequateFunctor.finiteFreeModule.{max u v w} A k)) := by
    apply (ULift.moduleEquiv.lTensor B).injective
    simpa using hTensor
  let castN : Fin (r + s) → Fin d.n := fun i => Fin.cast (by rfl) i
  let basisN (i : Fin d.n) :
      ↑(AdequateFunctor.finiteFreeModule.{max u v w} A d.n) :=
    ULift.up.{max u v w, u} (Pi.single i (1 : A))
  let zLeft : ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).obj
      (AdequateFunctor.finiteFreeModule.{max u v w} A d.n)).obj X :=
    (∑ i, b i ⊗ₜ[A] basisN (castN (Fin.castAdd s i)))
  let zRight : ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).obj
      (AdequateFunctor.finiteFreeModule.{max u v w} A d.n)).obj X :=
      ∑ j, c j ⊗ₜ[A] basisN (castN (Fin.natAdd r j))
  let z : ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).obj
      (AdequateFunctor.finiteFreeModule.{max u v w} A d.n)).obj X := zLeft + zRight
  have hQLleft' (i : Fin r) :
      diagramQLinear.{u, max u v w} M N φ d
          (Pi.single (castN (Fin.castAdd s i)) (1 : A)) = α (Pi.single i (1 : A)) := by
    simpa [castN] using hQLleft i
  have hQLright' (j : Fin s) :
      diagramQLinear.{u, max u v w} M N φ d
          (Pi.single (castN (Fin.natAdd r j)) (1 : A)) = -ρ (v₀ j) := by
    simpa [castN] using hQLright j
  have hGLleft' (i : Fin r) :
      diagramGLinear.{u, max u v w} M N φ d
          (Pi.single (castN (Fin.castAdd s i)) (1 : A)) = m i := by
    simpa [castN] using hGLleft i
  have hGLright' (j : Fin s) :
      diagramGLinear.{u, max u v w} M N φ d
          (Pi.single (castN (Fin.natAdd r j)) (1 : A)) = 0 := by
    simpa [castN] using hGLright j
  refine ⟨d, z, ?_, ?_⟩
  · change (((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map
      (liftFreeMap.{u, v, w} (A := A) d.n d.m
          (diagramQLinear.{u, max u v w} M N φ d))).app X).hom z = 0
    rw [show z = zLeft + zRight by rfl]
    rw [(((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map
      (liftFreeMap.{u, v, w} (A := A) d.n d.m
        (diagramQLinear.{u, max u v w} M N φ d))).app X).hom.map_add zLeft zRight,
      map_sum, map_sum]
    change (∑ i : Fin r, b i ⊗ₜ[A]
        (ULift.up (diagramQLinear.{u, max u v w} M N φ d
          (Pi.single (castN (Fin.castAdd s i)) (1 : A))) :
            ↑(AdequateFunctor.finiteFreeModule.{max u v w} A d.m))) +
      (∑ j : Fin s, c j ⊗ₜ[A]
        (ULift.up (diagramQLinear.{u, max u v w} M N φ d
          (Pi.single (castN (Fin.natAdd r j)) (1 : A))) :
            ↑(AdequateFunctor.finiteFreeModule.{max u v w} A d.m))) = 0
    have hleft :
        (∑ i : Fin r, b i ⊗ₜ[A]
          (ULift.up (diagramQLinear.{u, max u v w} M N φ d
            (Pi.single (castN (Fin.castAdd s i)) (1 : A))))) =
          ∑ i : Fin r, b i ⊗ₜ[A] (ULift.up (α (Pi.single i (1 : A)))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hQLleft' i]
    have hright :
        (∑ j : Fin s, c j ⊗ₜ[A]
          (ULift.up (diagramQLinear.{u, max u v w} M N φ d
            (Pi.single (castN (Fin.natAdd r j)) (1 : A))))) =
          ∑ j : Fin s, c j ⊗ₜ[A] (ULift.up (-ρ (v₀ j))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hQLright' j]
    rw [hleft, hright]
    rw [hTensorUp]
    change (∑ j : Fin s, c j ⊗ₜ[A] (ULift.up (ρ (v₀ j)))) +
      (∑ j : Fin s, c j ⊗ₜ[A] (-(ULift.up (ρ (v₀ j)))) ) = 0
    have hneg :
        (∑ j : Fin s, c j ⊗ₜ[A] (-(ULift.up (ρ (v₀ j))))) =
          -(∑ j : Fin s, c j ⊗ₜ[A] (ULift.up (ρ (v₀ j)))) := by
      calc
        (∑ j : Fin s, c j ⊗ₜ[A] (-(ULift.up (ρ (v₀ j))))) =
            ∑ j : Fin s, -(c j ⊗ₜ[A] ULift.up (ρ (v₀ j))) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [TensorProduct.tmul_neg]
        _ = -(∑ j : Fin s, c j ⊗ₜ[A] ULift.up (ρ (v₀ j))) := by
              rw [Finset.sum_neg_distrib]
    rw [hneg]
    exact add_neg_cancel _
  · change (((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map
      (liftFreeToModule.{u, v, w} (A := A) d.n (diagramGLinear.{u, max u v w} M N φ d))).app X).hom
        z = w₀
    rw [show z = zLeft + zRight by rfl]
    rw [(((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map
      (liftFreeToModule.{u, v, w} (A := A) d.n
        (diagramGLinear.{u, max u v w} M N φ d))).app X).hom.map_add zLeft zRight,
      map_sum, map_sum]
    change (∑ i : Fin r, b i ⊗ₜ[A]
        diagramGLinear.{u, max u v w} M N φ d
          (Pi.single (castN (Fin.castAdd s i)) (1 : A))) +
      (∑ j : Fin s, c j ⊗ₜ[A]
        diagramGLinear.{u, max u v w} M N φ d
          (Pi.single (castN (Fin.natAdd r j)) (1 : A))) = w₀
    have hleft :
        (∑ i : Fin r, b i ⊗ₜ[A]
          diagramGLinear.{u, max u v w} M N φ d
            (Pi.single (castN (Fin.castAdd s i)) (1 : A))) =
          ∑ i : Fin r, b i ⊗ₜ[A] m i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hGLleft' i]
    have hright :
        (∑ j : Fin s, c j ⊗ₜ[A]
          diagramGLinear.{u, max u v w} M N φ d
            (Pi.single (castN (Fin.natAdd r j)) (1 : A))) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hGLright' j]
      simp
    rw [hleft, hright, add_zero, hw]

/-- An adequate functor is a pointwise quotient of a direct sum of
linearly adequate functors. -/
@[stacks 06UX]
public lemma exists_coproduct_linearlyAdequate_surjective
    {A : Type u} [CommRing A]
    (F : AdequateFunctor.ModuleValuedFunctor.{w, v} A)
    (hF : AdequateFunctor.IsAdequate (𝟭 _) F) :
    ∃ (ι : Type (max u v w))
      (L : ι → AdequateFunctor.ModuleValuedFunctor.{max u v w, v} A),
      (∀ i, AdequateFunctor.IsLinearlyAdequate (𝟭 _) (L i)) ∧
        ∃ (f : (∐ L) ⟶
          (AdequateFunctor.presheafOfModulesUliftFunctor.{max u v, w}
            (AdequateFunctor.algebraRingDiagram.{v} A)).obj F),
          ∀ X, Function.Surjective (f.app X) := by
      classical
      let : Small.{max u v w} A := inferInstance
      obtain ⟨M, N, φ, ⟨e⟩⟩ := hF
      let U := AdequateFunctor.presheafOfModulesUliftFunctor.{max u v, w}
        (AdequateFunctor.algebraRingDiagram.{v} A)
      change U.obj F ≅ kernel ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map φ) at e
      let ι : Type (max u v w) :=
        FiniteKernelDiagram.{u, max u v w} M N φ
      let L : ι → AdequateFunctor.ModuleValuedFunctor.{max u v w, v} A := fun d =>
        kernel (diagramQ.{u, v, w} d)
      have hL (d : ι) : AdequateFunctor.IsLinearlyAdequate (𝟭 _) (L d) :=
        (AdequateFunctor.isLinearlyAdequate_iff (A := A) (F := L d)).2
          ⟨d.n, d.m, diagramQ.{u, v, w} d, ⟨Iso.refl _⟩⟩
      let g : (d : ι) → L d ⟶ U.obj F := fun d =>
        finiteKernelDiagramMap.{u, v, w} F e d
      let f : (∐ L) ⟶ U.obj F := Sigma.desc g
      refine ⟨ι, L, hL, f, fun X y ↦ ?_⟩
      obtain ⟨d, z, hzq, hzg⟩ := exists_diagram_tensor_preimage F e X y
      let q := diagramQ.{u, v, w} d
      obtain ⟨zL, hinc⟩ := exists_kernel_ι_app_eq q X z hzq
      refine ⟨(Sigma.ι L d).app X zL, ?_⟩
      change (Sigma.ι L d ≫ f).app X zL = y
      rw [Sigma.ι_comp_desc]
      have hinj : Function.Injective (e.hom.app X) :=
        ModuleCat.mono_iff_injective _ |>.mp inferInstance
      apply hinj
      dsimp [g, finiteKernelDiagramMap, q]
      have hki : Function.Injective
          ((kernel.ι ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map φ)).app X) :=
        ModuleCat.mono_iff_injective _ |>.mp inferInstance
      apply hki
      change
        (((kernel.ι ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map φ)).app X).hom
        ((e.hom.app X).hom ((g d).app X zL))) =
        (((kernel.ι ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map φ)).app X).hom
          ((e.hom.app X).hom y))
      have hmap :
          (g d) ≫ e.hom ≫
              kernel.ι ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map φ) =
            kernel.ι q ≫ diagramG d := by
        simp [g, finiteKernelDiagramMap, q, Category.assoc]
      have hmapX := congrArg (fun f => f.app X) hmap
      have hmapZ := congrArg (fun f => f.hom zL) hmapX
      have hmapZ' :
          (((kernel.ι ((AdequateFunctor.moduleExtensionFunctor.{max u v w, v} A).map φ)).app X).hom
            ((e.hom.app X).hom ((g d).app X zL))) =
          (diagramG d).app X z := by
        calc
          _ = ((kernel.ι q ≫ diagramG d).app X).hom zL := hmapZ
          _ = (diagramG d).app X z := by
            change (diagramG d).app X (((kernel.ι q).app X).hom zL) = _
            rw [hinc]
      exact hmapZ'.trans hzg

end

end AdequateFunctor

end
