module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Adequate.Tangent.TangentFunctor

/-!
# Permanence of right exactness of the tangent functor

Right exactness of the tangent functor is inherited along short exact sequences of
module-valued functors (extensions and quotients) and by pullbacks.

## References

* [Stacks Project, Tag 06ZF](https://stacks.math.columbia.edu/tag/06ZF)
-/

@[expose] public section

namespace AdequateFunctor

section

open CategoryTheory

universe u v w


open AdequateFunctor AdequateFunctor.AlgebraModulePair

variable {A : Type u} [CommRing A]

/-- The map on tangent modules induced by a morphism of module-valued functors. -/
public noncomputable def tangentModuleMap
    {F G : PresheafOfModules.{w} (algebraStructurePresheaf.{v} A)} (α : F ⟶ G)
    (X : AlgebraModulePair.{v} A) :
    tangentModule A F X →ₗ[X.algebra] tangentModule A G X where
  toFun x := ⟨α.app _ x, by
    rw [mem_tangentKernel]
    change G.map ((CommAlgCat.ofHom (squareZeroAugmentation A X)).op.op) (α.app _ x) = 0
    rw [← PresheafOfModules.naturality_apply α]
    rw [show F.map ((CommAlgCat.ofHom (squareZeroAugmentation A X)).op.op) x = 0 from x.2]
    change (α.app (Opposite.op (Opposite.op (CommAlgCat.of A X.algebra)))).hom
      (0 : F.obj (Opposite.op (Opposite.op (CommAlgCat.of A X.algebra)))) = 0
    exact (α.app (Opposite.op (Opposite.op (CommAlgCat.of A X.algebra)))).hom.map_zero⟩
  map_add' x y := by
    apply @Subtype.ext (extensionValue A G X) (fun z => z ∈ tangentKernel A G X)
    exact map_add _ _ _
  map_smul' r x := by
    apply @Subtype.ext (extensionValue A G X) (fun z => z ∈ tangentKernel A G X)
    change α.app _ (squareZeroSection A X r • (x : extensionValue A F X)) =
      squareZeroSection A X r • α.app _ (x : extensionValue A F X)
    exact map_smul _ _ _

/-- A short exact sequence of presheaves of modules is exact on sections at every object. -/
private lemma app_exact_of_shortExact
    {S : ShortComplex (PresheafOfModules.{w} (algebraStructurePresheaf.{v} A))}
    (hS : S.ShortExact) (Q) : Function.Exact (S.f.app Q) (S.g.app Q) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (hS.exact.map (PresheafOfModules.evaluation (algebraStructurePresheaf.{v} A) Q))

private lemma tangentModuleMap_properties
    (S : ShortComplex (PresheafOfModules.{w} (algebraStructurePresheaf.{v} A)))
    (hS : S.ShortExact) (X : AlgebraModulePair.{v} A) :
    Function.Injective (tangentModuleMap S.f X) ∧
      Function.Exact (tangentModuleMap S.f X) (tangentModuleMap S.g X) ∧
      Function.Surjective (tangentModuleMap S.g X) := by
  let := hS.mono_f
  let := hS.epi_g
  have exactAt (Q) : Function.Exact (S.f.app Q) (S.g.app Q) := app_exact_of_shortExact hS Q
  have nat {F G : PresheafOfModules.{w} (algebraStructurePresheaf.{v} A)}
      (α : F ⟶ G) (x : extensionValue A F X) :
      moduleValueMap A G (squareZeroAugmentation A X) (α.app _ x) =
        α.app _ (moduleValueMap A F (squareZeroAugmentation A X) x) := by
    exact (PresheafOfModules.naturality_apply α
      ((CommAlgCat.ofHom (squareZeroAugmentation A X)).op.op) x).symm
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply PresheafOfModules.injective_of_mono S.f _
    exact congrArg Subtype.val hxy
  constructor
  · intro y
    constructor
    · intro hy
      have hy' : S.g.app _ (y : extensionValue A S.X₂ X) = 0 :=
        congrArg Subtype.val hy
      obtain ⟨x, hx⟩ := (exactAt
        (Opposite.op (Opposite.op (CommAlgCat.of A (squareZeroAlgebra A X))))
        (y : extensionValue A S.X₂ X)).mp hy'
      have hax : moduleValueMap A S.X₁ (squareZeroAugmentation A X) x = 0 := by
        apply PresheafOfModules.injective_of_mono S.f _
        change S.f.app _ _ = S.f.app _ 0
        rw [← nat S.f x, hx, y.2, map_zero]
      exact ⟨⟨x, hax⟩, Subtype.ext hx⟩
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      exact (exactAt
        (Opposite.op (Opposite.op (CommAlgCat.of A (squareZeroAlgebra A X))))
        (S.f.app _ (x : extensionValue A S.X₁ X))).mpr
          ⟨(x : extensionValue A S.X₁ X), rfl⟩
  · intro z
    obtain ⟨y, hy⟩ := PresheafOfModules.surjective_of_epi S.g _
      (z : extensionValue A S.X₃ X)
    have hay : S.g.app _ (moduleValueMap A S.X₂ (squareZeroAugmentation A X) y) = 0 := by
      rw [← nat S.g y, hy]
      exact z.2
    obtain ⟨x, hx⟩ := (exactAt
      (Opposite.op (Opposite.op (CommAlgCat.of A X.algebra))) _).mp hay
    let x' : extensionValue A S.X₁ X :=
      moduleValueMap A S.X₁ (squareZeroSection A X) x
    have hsection : moduleValueMap A S.X₁ (squareZeroAugmentation A X) x' = x := by
      rw [← tangentDecomposition_fst]
      have h := congrArg (tangentDecomposition A S.X₁ X)
        ((tangentDecompositionData A S.X₁ X).property x 0)
      simpa [x'] using congrArg Prod.fst h.symm
    have htan : y - S.f.app _ x' ∈ tangentKernel A S.X₂ X := by
      rw [mem_tangentKernel, map_sub, nat S.f x', hsection, hx, sub_self]
    refine ⟨⟨y - S.f.app _ x', htan⟩, ?_⟩
    apply Subtype.ext
    change S.g.app _ (y - S.f.app _ x') = (z : extensionValue A S.X₃ X)
    have hz : S.g.app
        (Opposite.op (Opposite.op (CommAlgCat.of A (squareZeroAlgebra A X))))
        (S.f.app _ x') = 0 :=
      (exactAt
        (Opposite.op (Opposite.op (CommAlgCat.of A (squareZeroAlgebra A X)))) _).mpr
          ⟨x', rfl⟩
    rw [map_sub, hz, sub_zero, hy]

/-- The left map in the tangent sequence of a short exact sequence is injective. -/
public lemma tangentModuleMap_injective
    (S : ShortComplex (PresheafOfModules.{w} (algebraStructurePresheaf.{v} A)))
    (hS : S.ShortExact) (X : AlgebraModulePair.{v} A) :
    Function.Injective (tangentModuleMap S.f X) :=
  (tangentModuleMap_properties S hS X).1

/-- The tangent sequence of a short exact sequence is exact at its middle term. -/
public lemma tangentModuleMap_exact
    (S : ShortComplex (PresheafOfModules.{w} (algebraStructurePresheaf.{v} A)))
    (hS : S.ShortExact) (X : AlgebraModulePair.{v} A) :
    Function.Exact (tangentModuleMap S.f X) (tangentModuleMap S.g X) :=
  (tangentModuleMap_properties S hS X).2.1

/-- The right map in the tangent sequence of a short exact sequence is surjective. -/
public lemma tangentModuleMap_surjective
    (S : ShortComplex (PresheafOfModules.{w} (algebraStructurePresheaf.{v} A)))
    (hS : S.ShortExact) (X : AlgebraModulePair.{v} A) :
    Function.Surjective (tangentModuleMap S.g X) :=
  (tangentModuleMap_properties S hS X).2.2

end

section

open CategoryTheory


open AdequateFunctor

universe u v w

variable {A : Type u} [CommRing A]

private theorem tangentModuleMap_naturality
    {F G : PresheafOfModules.{w} (algebraStructurePresheaf.{v} A)}
    (α : F ⟶ G) {X Y : AlgebraModulePair.{v} A}
    (f : X ⟶ Y) (x : tangentModule A F X) :
    tangentModuleMap α Y ((tangentFunctor A F).map f x) =
      ((tangentFunctor A G).map f) (tangentModuleMap α X x) := by
  apply Subtype.ext
  change α.app _ ((tangentFunctor A F).map f x) =
    ((tangentFunctor A G).map f (tangentModuleMap α X x) : extensionValue A G Y)
  rw [(tangentFunctor A F).map_coe, (tangentFunctor A G).map_coe]
  exact PresheafOfModules.naturality_apply α
    ((CommAlgCat.ofHom (squareZeroMap A f)).op.op) (x : extensionValue A F X)

private theorem right_exact_middle_of_exact_columns
    {F₁ F₂ F₃ G₁ G₂ G₃ H₁ H₂ H₃ : Type u}
    [AddCommGroup F₁] [AddCommGroup F₂] [AddCommGroup F₃]
    [AddCommGroup G₁] [AddCommGroup G₂] [AddCommGroup G₃]
    [AddCommGroup H₁] [AddCommGroup H₂] [AddCommGroup H₃]
    (fi₁ : F₁ →+ G₁) (fi₂ : F₂ →+ G₂) (fi₃ : F₃ →+ G₃)
    (ph₁ : G₁ →+ H₁) (ph₂ : G₂ →+ H₂) (ph₃ : G₃ →+ H₃)
    (ff : F₁ →+ F₂) (fg : F₂ →+ F₃)
    (gf : G₁ →+ G₂) (gg : G₂ →+ G₃)
    (hf : H₁ →+ H₂) (hg : H₂ →+ H₃)
    (hinj₃ : Function.Injective fi₃)
    (hex₂ : Function.Exact fi₂ ph₂) (hex₃ : Function.Exact fi₃ ph₃)
    (hsurj₁ : Function.Surjective ph₁) (hsurj₂ : Function.Surjective ph₂)
    (hFexact : Function.Exact ff fg) (hFsurj : Function.Surjective fg)
    (hHexact : Function.Exact hf hg) (hHsurj : Function.Surjective hg)
    (comm_if : ∀ x, fi₂ (ff x) = gf (fi₁ x))
    (comm_ig : ∀ x, fi₃ (fg x) = gg (fi₂ x))
    (comm_pf : ∀ x, ph₂ (gf x) = hf (ph₁ x))
    (comm_pg : ∀ x, ph₃ (gg x) = hg (ph₂ x))
    (hGzero : ∀ x, gg (gf x) = 0) :
    Function.Exact gf gg ∧ Function.Surjective gg := by
  constructor
  · intro y
    constructor
    · intro hy
      have hzero : hg (ph₂ y) = 0 := by
        rw [← comm_pg, hy, map_zero]
      obtain ⟨z, hz⟩ := (hHexact (ph₂ y)).mp hzero
      obtain ⟨x, hx⟩ := hsurj₁ z
      let y' := y - gf x
      have hpy' : ph₂ y' = 0 := by
        dsimp [y']
        rw [map_sub, comm_pf, hx, hz, sub_self]
      obtain ⟨t, ht⟩ := (hex₂ y').mp hpy'
      have hgft : fg t = 0 := hinj₃ (by
        calc
          fi₃ (fg t) = gg (fi₂ t) := comm_ig t
          _ = gg y' := congrArg gg ht
          _ = gg y - gg (gf x) := by dsimp [y']; exact map_sub _ _ _
          _ = 0 := by rw [hy, hGzero, sub_self]
          _ = fi₃ 0 := (map_zero fi₃).symm)
      obtain ⟨q, hq⟩ := (hFexact t).mp hgft
      refine ⟨fi₁ q + x, ?_⟩
      calc
        gf (fi₁ q + x) = gf (fi₁ q) + gf x := map_add _ _ _
        _ = fi₂ (ff q) + gf x := by rw [comm_if]
        _ = fi₂ t + gf x := by rw [hq]
        _ = y := by rw [ht]; dsimp [y']; exact sub_add_cancel y (gf x)
    · rintro ⟨x, rfl⟩
      exact hGzero x
  · intro z
    obtain ⟨t, ht⟩ := hHsurj (ph₃ z)
    obtain ⟨y, hy⟩ := hsurj₂ t
    let z' := z - gg y
    have hpz' : ph₃ z' = 0 := by
      dsimp [z']
      rw [map_sub, comm_pg, hy, ht, sub_self]
    obtain ⟨q, hq⟩ := (hex₃ z').mp hpz'
    obtain ⟨r, hr⟩ := hFsurj q
    refine ⟨y + fi₂ r, ?_⟩
    calc
      gg (y + fi₂ r) = gg y + gg (fi₂ r) := map_add _ _ _
      _ = gg y + fi₃ (fg r) := by rw [← comm_ig]
      _ = gg y + fi₃ q := by rw [hr]
      _ = z := by
        rw [hq]
        dsimp [z']
        abel

/-- Property `(*)` is stable under extensions of module-valued functors. -/
@[stacks 06ZF "extension_permanence"]
theorem rightExactTangentFunctor_of_shortExact
    (S : ShortComplex (PresheafOfModules.{w} (algebraStructurePresheaf.{v} A)))
    (hS : S.ShortExact)
    (hF : HasRightExactTangentFunctor A S.X₁)
    (hH : HasRightExactTangentFunctor A S.X₃) :
    HasRightExactTangentFunctor A S.X₂ := by
  intro B _ _ T hT
  let P₁ := (fixedAlgebraModuleFunctor A B).obj T.X₁
  let P₂ := (fixedAlgebraModuleFunctor A B).obj T.X₂
  let P₃ := (fixedAlgebraModuleFunctor A B).obj T.X₃
  let R₁ := T.map (tangentFunctorAt A S.X₁ B)
  let R₂ := T.map (tangentFunctorAt A S.X₂ B)
  let R₃ := T.map (tangentFunctorAt A S.X₃ B)
  let fi₁ : R₁.X₁ →+ R₂.X₁ := (tangentModuleMap S.f P₁).toAddMonoidHom
  let fi₂ : R₁.X₂ →+ R₂.X₂ := (tangentModuleMap S.f P₂).toAddMonoidHom
  let fi₃ : R₁.X₃ →+ R₂.X₃ := (tangentModuleMap S.f P₃).toAddMonoidHom
  let ph₁ : R₂.X₁ →+ R₃.X₁ := (tangentModuleMap S.g P₁).toAddMonoidHom
  let ph₂ : R₂.X₂ →+ R₃.X₂ := (tangentModuleMap S.g P₂).toAddMonoidHom
  let ph₃ : R₂.X₃ →+ R₃.X₃ := (tangentModuleMap S.g P₃).toAddMonoidHom
  let ff : R₁.X₁ →+ R₁.X₂ := ConcreteCategory.hom R₁.f
  let fg : R₁.X₂ →+ R₁.X₃ := ConcreteCategory.hom R₁.g
  let gf : R₂.X₁ →+ R₂.X₂ := ConcreteCategory.hom R₂.f
  let gg : R₂.X₂ →+ R₂.X₃ := ConcreteCategory.hom R₂.g
  let hf : R₃.X₁ →+ R₃.X₂ := ConcreteCategory.hom R₃.f
  let hg : R₃.X₂ →+ R₃.X₃ := ConcreteCategory.hom R₃.g
  have hinj₃ : Function.Injective fi₃ := tangentModuleMap_injective S hS P₃
  have hex₂ : Function.Exact fi₂ ph₂ := tangentModuleMap_exact S hS P₂
  have hex₃ : Function.Exact fi₃ ph₃ := tangentModuleMap_exact S hS P₃
  have hsurj₁ : Function.Surjective ph₁ := tangentModuleMap_surjective S hS P₁
  have hsurj₂ : Function.Surjective ph₂ := tangentModuleMap_surjective S hS P₂
  have hF₁ := hF B T hT
  have hFexact : Function.Exact ff fg := (R₁.ab_exact_iff_function_exact).mp hF₁.1
  have hFsurj : Function.Surjective fg := (AddCommGrpCat.epi_iff_surjective R₁.g).mp hF₁.2
  have hH₃ := hH B T hT
  have hHexact : Function.Exact hf hg := (R₃.ab_exact_iff_function_exact).mp hH₃.1
  have hHsurj : Function.Surjective hg := (AddCommGrpCat.epi_iff_surjective R₃.g).mp hH₃.2
  have comm_if : ∀ x, fi₂ (ff x) = gf (fi₁ x) := by
    intro x
    exact tangentModuleMap_naturality S.f ((fixedAlgebraModuleFunctor A B).map T.f) x
  have comm_ig : ∀ x, fi₃ (fg x) = gg (fi₂ x) := by
    intro x
    exact tangentModuleMap_naturality S.f ((fixedAlgebraModuleFunctor A B).map T.g) x
  have comm_pf : ∀ x, ph₂ (gf x) = hf (ph₁ x) := by
    intro x
    exact tangentModuleMap_naturality S.g ((fixedAlgebraModuleFunctor A B).map T.f) x
  have comm_pg : ∀ x, ph₃ (gg x) = hg (ph₂ x) := by
    intro x
    exact tangentModuleMap_naturality S.g ((fixedAlgebraModuleFunctor A B).map T.g) x
  have hGzero : ∀ x, gg (gf x) = 0 := by
    intro x
    simp [gf, gg]
  have hresult := right_exact_middle_of_exact_columns
    fi₁ fi₂ fi₃ ph₁ ph₂ ph₃ ff fg gf gg hf hg
    hinj₃ hex₂ hex₃ hsurj₁ hsurj₂ hFexact hFsurj hHexact hHsurj
    comm_if comm_ig comm_pf comm_pg hGzero
  exact ⟨(R₂.ab_exact_iff_function_exact).mpr hresult.1,
    (AddCommGrpCat.epi_iff_surjective R₂.g).mpr hresult.2⟩

end

section

open CategoryTheory


universe u v w

private lemma rightExact_third_of_diagram
    {F₂ F₃ G₁ G₂ G₃ H₁ H₂ H₃ : Type*}
    [AddCommGroup F₂] [AddCommGroup F₃]
    [AddCommGroup G₁] [AddCommGroup G₂] [AddCommGroup G₃]
    [AddCommGroup H₁] [AddCommGroup H₂] [AddCommGroup H₃]
    (q₁ : G₁ →+ H₁) (q₂ : G₂ →+ H₂) (q₃ : G₃ →+ H₃)
    (p₂ : F₂ →+ G₂) (p₃ : F₃ →+ G₃)
    (gF : F₂ →+ F₃)
    (fG : G₁ →+ G₂) (gG : G₂ →+ G₃)
    (fH : H₁ →+ H₂) (gH : H₂ →+ H₃)
    (hq₂ : Function.Surjective q₂) (hq₃ : Function.Surjective q₃)
    (hex₃ : Function.Exact p₃ q₃) (hqp₂ : ∀ x, q₂ (p₂ x) = 0)
    (hgF : Function.Surjective gF)
    (hexG : Function.Exact fG gG) (hgG : Function.Surjective gG)
    (hcomm₁ : ∀ y, q₂ (fG y) = fH (q₁ y))
    (hcomm₂ : ∀ y, q₃ (gG y) = gH (q₂ y))
    (hcomm₃ : ∀ x, gG (p₂ x) = p₃ (gF x))
    (hcompH : ∀ x, gH (fH x) = 0) :
    Function.Exact fH gH ∧ Function.Surjective gH := by
  constructor
  · intro z
    constructor
    · intro hz
      obtain ⟨y, hy⟩ := hq₂ z
      have hzero : q₃ (gG y) = 0 := by rw [hcomm₂, hy, hz]
      obtain ⟨x₃, hx₃⟩ := (hex₃ (gG y)).mp hzero
      obtain ⟨x₂, hx₂⟩ := hgF x₃
      have hyzero : gG (y - p₂ x₂) = 0 := by
        rw [map_sub, hcomm₃, hx₂, hx₃, sub_self]
      obtain ⟨y₁, hy₁⟩ := (hexG (y - p₂ x₂)).mp hyzero
      refine ⟨q₁ y₁, ?_⟩
      calc
        fH (q₁ y₁) = q₂ (fG y₁) := (hcomm₁ y₁).symm
        _ = q₂ (y - p₂ x₂) := by rw [hy₁]
        _ = z := by rw [map_sub, hqp₂, sub_zero, hy]
    · rintro ⟨y, rfl⟩
      exact hcompH y
  · intro z
    obtain ⟨y₃, hy₃⟩ := hq₃ z
    obtain ⟨y₂, hy₂⟩ := hgG y₃
    exact ⟨q₂ y₂, by rw [← hcomm₂, hy₂, hy₃]⟩

/-- Property `(*)` passes to the quotient in a short exact sequence of
module-valued functors. -/
@[stacks 06ZF "quotient_permanence"]
public lemma hasRightExactTangentFunctor_of_shortExact
    (A : Type u) [CommRing A]
    (S : ShortComplex (PresheafOfModules.{w} (AdequateFunctor.algebraStructurePresheaf.{v} A)))
    (hS : S.ShortExact)
    (hF : AdequateFunctor.HasRightExactTangentFunctor A S.X₁)
    (hG : AdequateFunctor.HasRightExactTangentFunctor A S.X₂) :
    AdequateFunctor.HasRightExactTangentFunctor A S.X₃ := by
  intro B _ _ T hT
  let fixed := AdequateFunctor.fixedAlgebraModuleFunctor A B
  let X₁ := fixed.obj T.X₁
  let X₂ := fixed.obj T.X₂
  let X₃ := fixed.obj T.X₃
  let q₁ := fixed.map T.f
  let q₂ := fixed.map T.g
  let gF := ((AdequateFunctor.tangentFunctor A S.X₁).map q₂).toAddMonoidHom
  let gG := ((AdequateFunctor.tangentFunctor A S.X₂).map q₂).toAddMonoidHom
  let gH := ((AdequateFunctor.tangentFunctor A S.X₃).map q₂).toAddMonoidHom
  let fG := ((AdequateFunctor.tangentFunctor A S.X₂).map q₁).toAddMonoidHom
  let fH := ((AdequateFunctor.tangentFunctor A S.X₃).map q₁).toAddMonoidHom
  let p₂ := (AdequateFunctor.tangentModuleMap S.f X₂).toAddMonoidHom
  let p₃ := (AdequateFunctor.tangentModuleMap S.f X₃).toAddMonoidHom
  let q₁' := (AdequateFunctor.tangentModuleMap S.g X₁).toAddMonoidHom
  let q₂' := (AdequateFunctor.tangentModuleMap S.g X₂).toAddMonoidHom
  let q₃' := (AdequateFunctor.tangentModuleMap S.g X₃).toAddMonoidHom
  have hGprop := hG B T hT
  have hgF : Function.Surjective gF := by
    change Function.Surjective ((AdequateFunctor.tangentFunctorAt A S.X₁ B).map T.g)
    exact (AddCommGrpCat.epi_iff_surjective _).mp (hF B T hT).2
  have hgG : Function.Surjective gG := by
    change Function.Surjective ((AdequateFunctor.tangentFunctorAt A S.X₂ B).map T.g)
    exact (AddCommGrpCat.epi_iff_surjective _).mp hGprop.2
  have hexG : Function.Exact fG gG := (ShortComplex.ab_exact_iff_function_exact _).mp hGprop.1
  have hqp₂ : ∀ x, q₂' (p₂ x) = 0 := by
    intro x
    apply Subtype.ext
    exact (app_exact_of_shortExact hS _ ((S.f.app _) (x : extensionValue A S.X₁ X₂))).2
      ⟨x, rfl⟩
  have hcompH : ∀ x, gH (fH x) = 0 := by
    intro x
    have hmap := AdequateFunctor.tangentFunctor_map_eq_zero A S.X₃ (q₁ ≫ q₂)
      (congrArg (fun k => k.hom) T.zero)
    change ((AdequateFunctor.tangentFunctor A S.X₃).map q₂)
      ((AdequateFunctor.tangentFunctor A S.X₃).map q₁ x) = 0
    rw [← (AdequateFunctor.tangentFunctor A S.X₃).map_comp]
    exact DFunLike.congr_fun hmap x
  have hdiag := rightExact_third_of_diagram q₁' q₂' q₃' p₂ p₃ gF fG gG fH gH
    (tangentModuleMap_surjective S hS X₂) (tangentModuleMap_surjective S hS X₃)
    (tangentModuleMap_exact S hS X₃) hqp₂ hgF hexG hgG
    (fun y => tangentModuleMap_naturality S.g q₁ y)
    (fun y => tangentModuleMap_naturality S.g q₂ y)
    (fun x => (tangentModuleMap_naturality S.f q₂ x).symm) hcompH
  exact ⟨(ShortComplex.ab_exact_iff_function_exact _).mpr hdiag.1,
    (AddCommGrpCat.epi_iff_surjective _).mpr hdiag.2⟩

end

section

open CategoryTheory CategoryTheory.Limits


open AdequateFunctor

universe u v w

private noncomputable def pullbackShortComplex
    {A : Type u} [CommRing A]
    (S : ShortComplex (PresheafOfModules.{w} (algebraStructurePresheaf.{v} A)))
    {H' : PresheafOfModules.{w} (algebraStructurePresheaf.{v} A)}
    (f : H' ⟶ S.X₃) :
    ShortComplex (PresheafOfModules.{w} (algebraStructurePresheaf.{v} A)) :=
  ShortComplex.mk (pullback.lift S.f 0 (S.zero.trans zero_comp.symm))
    (pullback.snd S.g f) (pullback.lift_snd S.f 0 _)

private lemma pullbackShortComplex_shortExact
    {A : Type u} [CommRing A]
    (S : ShortComplex (PresheafOfModules.{w} (algebraStructurePresheaf.{v} A)))
    (hS : S.ShortExact)
    {H' : PresheafOfModules.{w} (algebraStructurePresheaf.{v} A)}
    (f : H' ⟶ S.X₃) : (pullbackShortComplex S f).ShortExact := by
  let i : S.X₁ ⟶ pullback S.g f :=
    pullback.lift S.f 0 (S.zero.trans zero_comp.symm)
  let T := pullbackShortComplex S f
  have hi : i ≫ pullback.snd S.g f = 0 := pullback.lift_snd S.f 0 _
  have hk₀ {W : PresheafOfModules.{w} (algebraStructurePresheaf.{v} A)}
      (k : W ⟶ pullback S.g f) (hk : k ≫ pullback.snd S.g f = 0) :
      (k ≫ pullback.fst S.g f) ≫ S.g = 0 := by
    calc
      (k ≫ pullback.fst S.g f) ≫ S.g = k ≫ (pullback.fst S.g f ≫ S.g) := by simp
      _ = k ≫ (pullback.snd S.g f ≫ f) := by rw [pullback.condition]
      _ = (k ≫ pullback.snd S.g f) ≫ f := by simp [Category.assoc]
      _ = 0 := by rw [hk, zero_comp]
  have hKer : IsLimit (KernelFork.ofι T.f T.zero) := by
    change IsLimit (KernelFork.ofι i hi)
    refine KernelFork.IsLimit.ofι i hi ?_ ?_ ?_
    · intro W k hk
      change W ⟶ pullback S.g f at k
      change k ≫ pullback.snd S.g f = 0 at hk
      exact (KernelFork.IsLimit.lift' hS.fIsKernel (k ≫ pullback.fst S.g f) (hk₀ k hk)).1
    · intro W k hk
      change W ⟶ pullback S.g f at k
      change k ≫ pullback.snd S.g f = 0 at hk
      have hk₁ := hk₀ k hk
      let m : W ⟶ S.X₁ := (KernelFork.IsLimit.lift' hS.fIsKernel (k ≫ pullback.fst S.g f) hk₁).1
      have hm : m ≫ S.f = k ≫ pullback.fst S.g f :=
        (KernelFork.IsLimit.lift' hS.fIsKernel (k ≫ pullback.fst S.g f) hk₁).2
      apply pullback.hom_ext
      · calc
          m ≫ i ≫ pullback.fst S.g f = m ≫ S.f := by simp [i]
          _ = k ≫ pullback.fst S.g f := hm
      · calc
          m ≫ i ≫ pullback.snd S.g f = m ≫ 0 := by simp [i]
          _ = k ≫ pullback.snd S.g f := by rw [hk, comp_zero]
    · intro W k hk m hm
      have := hS.mono_f
      change W ⟶ pullback S.g f at k
      change k ≫ pullback.snd S.g f = 0 at hk
      have hk₁ := hk₀ k hk
      apply (cancel_mono S.f).1
      calc
        m ≫ S.f = m ≫ i ≫ pullback.fst S.g f := by
          simp [i]
        _ = k ≫ pullback.fst S.g f := congrArg (fun x => x ≫ pullback.fst S.g f) hm
        _ = (KernelFork.IsLimit.lift' hS.fIsKernel (k ≫ pullback.fst S.g f) hk₁).1 ≫ S.f :=
          (KernelFork.IsLimit.lift' hS.fIsKernel (k ≫ pullback.fst S.g f) hk₁).2.symm
  let : Epi S.g := hS.epi_g
  have : Epi (pullback.snd S.g f) := Abelian.epi_pullback_of_epi_f S.g f
  exact {
    exact := T.exact_of_f_is_kernel hKer
    mono_f := mono_of_isLimit_fork hKer
    epi_g := by
      simpa [T, pullbackShortComplex] using (inferInstance : Epi (pullback.snd S.g f)) }

/-- Property `(*)` passes to a pullback of a short exact sequence of
module-valued functors. -/
@[stacks 06ZF "pullback_permanence"]
public theorem hasRightExactTangentFunctor_pullback
    {A : Type u} [CommRing A]
    (S : ShortComplex (PresheafOfModules.{w} (algebraStructurePresheaf.{v} A)))
    (hS : S.ShortExact)
    {H' : PresheafOfModules.{w} (algebraStructurePresheaf.{v} A)}
    (f : H' ⟶ S.X₃)
    (hF : HasRightExactTangentFunctor A S.X₁)
    (hH' : HasRightExactTangentFunctor A H') :
    HasRightExactTangentFunctor A (pullback S.g f) := by
  let T := pullbackShortComplex S f
  have hT := pullbackShortComplex_shortExact S hS f
  have hF' : HasRightExactTangentFunctor A T.X₁ := by
    simpa [T, pullbackShortComplex] using hF
  simpa [T, pullbackShortComplex] using rightExactTangentFunctor_of_shortExact T hT hF' hH'

end

end AdequateFunctor

end
