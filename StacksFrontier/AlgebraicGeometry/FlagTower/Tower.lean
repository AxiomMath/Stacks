module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection.RestrictedSection
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.OverQuotients
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.FlagTower.Flag

/-!
# The tower of projective bundles of tautological kernels and its functor of points

Let `ℰ` be a finite locally free module on a scheme `X`. The projective bundle
`π : 𝐏(ℰ) ⟶ X` carries the tautological surjection `π^*ℰ ⟶ 𝒪(1)`, whose kernel `ℰ'` is again
finite locally free. Iterating, `Stacks.FlagTower.tower m ℰ` is the scheme over `X`

  `𝐏(ℰ^{(m-1)}) ⟶ ⋯ ⟶ 𝐏(ℰ') ⟶ 𝐏(ℰ) ⟶ X`,

a composition of `m` projective space bundles, each built on the tautological kernel of the
previous one. It is the partial flag variety of `ℰ`: **for a scheme `f : T ⟶ X` over `X`, the
morphisms `T ⟶ tower m ℰ` over `X` are the flags of length `m` of `f^*ℰ`**
(`Stacks.FlagTower.towerEquiv`), i.e. the chains of subobjects `K₀ ⊇ ⋯ ⊇ K_{m-1}` of `f^*ℰ`
with `f^*ℰ / K_i` finite locally free of rank `i + 1`; and this description is natural in `T`
(`Stacks.FlagTower.towerEquiv_comp`).

The first step is the universal property of `𝐏(ℰ)` (`Stacks.Chow.bundleOverEquiv`): a morphism
`g : T ⟶ 𝐏(ℰ)` over `f` is an invertible quotient of `f^*ℰ`, whose kernel is the image of
`g^*ℰ' ⟶ g^*π^*ℰ ≅ f^*ℰ` (`Stacks.FlagTower.kernelMapAlong`). The rest of the tower is the tower
over `𝐏(ℰ)` built on `ℰ'`, whose points over `g` are by induction the flags of `g^*ℰ'`, i.e. the
flags of `f^*ℰ` starting below that kernel.

## Main definitions

* `Stacks.FlagTower.tower m ℰ`: the tower, as an object of `Over X`.
* `Stacks.FlagTower.kernelMapAlong`: the inclusion `g^*ℰ' ⟶ f^*ℰ` along `g : T ⟶ 𝐏(ℰ)` over `f`.
* `Stacks.FlagTower.towerEquiv`: the morphisms into the tower over `f` are the flags of `f^*ℰ`.

## Main results

* `Stacks.FlagTower.towerEquiv_succ_apply`: the flag of a morphism into the tower of length
  `m + 1`, read off the first layer and the rest.
* `Stacks.FlagTower.towerEquiv_comp`: naturality in the test scheme.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 0FIQ](https://stacks.math.columbia.edu/tag/0FIQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.FlagTower

/-! ### The tautological kernel -/

section Kernel

variable {X : Scheme.{u}} (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The tautological kernel `ℰ'` of the projective bundle is finite locally free**: the
kernel of an epimorphism from a finite locally free module onto an invertible one. -/
instance isFiniteLocallyFree_kernel_bundleTautological :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (kernel (bundleTautological E)) :=
  Stacks.ProjectiveBundleSplitting.isFiniteLocallyFree_kernel_of_epi_isInvertible _
    inferInstance
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme _ E inferInstance)
    (isInvertible_bundleTwist E)

/-- The tautological sequence `0 ⟶ ℰ' ⟶ π^*ℰ ⟶ 𝒪(1) ⟶ 0` stays short exact after pullback
along any morphism, the quotient being locally free. -/
theorem shortExact_pullback_kernel_bundleTautological {T : Scheme.{u}} (g : T ⟶ bundle E) :
    ((ShortComplex.mk (kernel.ι (bundleTautological E)) (bundleTautological E)
      (kernel.condition _)).map (Scheme.Modules.pullback g)).ShortExact := by
  exact shortExact_map_pullback_kernelSequence_of_isLocallyFree g _ inferInstance
    (isLocallyFree_of_rank (Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist E))

variable {T : Scheme.{u}} {f : T ⟶ X}

/-- **The inclusion of the pulled back tautological kernel**: along `g : T ⟶ 𝐏(ℰ)` over
`f : T ⟶ X`, the map `g^*ℰ' ⟶ g^*π^*ℰ ≅ f^*ℰ`. -/
def kernelMapAlong (g : T ⟶ bundle E) (hg : g ≫ bundleProj E = f) :
    (Scheme.Modules.pullback g).obj (kernel (bundleTautological E)) ⟶
      (Scheme.Modules.pullback f).obj E :=
  (Scheme.Modules.pullback g).map (kernel.ι (bundleTautological E)) ≫
    (Scheme.Modules.pullbackComp g (bundleProj E)).hom.app E ≫
    (Scheme.Modules.pullbackCongr hg).hom.app E

/-- **The quotient a morphism into `𝐏(ℰ)` pulls back** from the tautological surjection:
`f^*ℰ ≅ (g ≫ π)^*ℰ ≅ g^*π^*ℰ ⟶ g^*𝒪(1)`. It is the quotient map of
`Stacks.Chow.bundleOverQuotient`. -/
def quotientAlong (g : T ⟶ bundle E) (hg : g ≫ bundleProj E = f) :
    (Scheme.Modules.pullback f).obj E ⟶ (Scheme.Modules.pullback g).obj (bundleTwist E) :=
  (Scheme.Modules.pullbackCongr hg).inv.app E ≫
    (Scheme.Modules.pullbackComp g (bundleProj E)).inv.app E ≫
    (Scheme.Modules.pullback g).map (bundleTautological E)

/-- The quotient map of `Stacks.Chow.bundleOverQuotient` is `quotientAlong`. -/
theorem bundleOverQuotient_q_eq (g : T ⟶ bundle E) (hg : g ≫ bundleProj E = f) :
    (bundleOverQuotient E g hg).q = quotientAlong E g hg := by
  rw [bundleOverQuotient_q]
  rfl

/-- The kernel inclusion followed by the quotient that `g` pulls back is zero. -/
theorem kernelMapAlong_comp_quotientAlong (g : T ⟶ bundle E) (hg : g ≫ bundleProj E = f) :
    kernelMapAlong E g hg ≫ quotientAlong E g hg = 0 := by
  simp only [kernelMapAlong, quotientAlong, Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp, kernel.condition, Functor.map_zero]

/-- The kernel inclusion followed by the quotient that `g` pulls back from the tautological
surjection is a short exact sequence. -/
theorem shortExact_kernelMapAlong (g : T ⟶ bundle E) (hg : g ≫ bundleProj E = f) :
    (ShortComplex.mk (kernelMapAlong E g hg) (quotientAlong E g hg)
      (kernelMapAlong_comp_quotientAlong E g hg)).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_ (shortExact_pullback_kernel_bundleTautological E g)
  refine ShortComplex.isoMk (Iso.refl _)
    ((Scheme.Modules.pullbackComp g (bundleProj E)).app E ≪≫
      (Scheme.Modules.pullbackCongr hg).app E) (Iso.refl _) ?_ ?_
  · simp [kernelMapAlong]
  · simp [quotientAlong]

/-- The kernel inclusion `g^*ℰ' ⟶ f^*ℰ` is a monomorphism. -/
instance mono_kernelMapAlong (g : T ⟶ bundle E) (hg : g ≫ bundleProj E = f) :
    Mono (kernelMapAlong E g hg) :=
  (shortExact_kernelMapAlong E g hg).mono_f

/-- The cokernel of the kernel inclusion is `g^*𝒪(1)`, of rank one. -/
theorem rank_cokernel_kernelMapAlong (g : T ⟶ bundle E) (hg : g ≫ bundleProj E = f) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (cokernel (kernelMapAlong E g hg)) 1 :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    (Stacks.Chow.GenuineChern.cokernelIsoOfShortExact (shortExact_kernelMapAlong E g hg)).symm
    (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ g _ _
      (Stacks.Chow.isFiniteLocallyFreeOfRank_bundleTwist E))

/-- A mono which is the kernel of an epi in a short exact sequence cuts out its kernel. -/
theorem mk_eq_kernelSubobject_of_shortExact {M A L : T.Modules} {i : A ⟶ M} {q : M ⟶ L}
    {w : i ≫ q = 0} (hS : (ShortComplex.mk i q w).ShortExact) :
    haveI := hS.mono_f
    Subobject.mk i = kernelSubobject q := by
  have := hS.mono_f
  refine le_antisymm (le_kernelSubobject _ _ (by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc, w, comp_zero])) ?_
  refine Subobject.le_mk_of_comm
    (hS.fIsKernel.lift (KernelFork.ofι _ (kernelSubobject_arrow_comp q))) ?_
  exact hS.fIsKernel.fac (KernelFork.ofι _ (kernelSubobject_arrow_comp q)) WalkingParallelPair.zero

/-- **The kernel of the quotient a morphism into `𝐏(ℰ)` pulls back is the image of the pulled
back tautological kernel.** -/
theorem mk_kernelMapAlong (g : T ⟶ bundle E) (hg : g ≫ bundleProj E = f) :
    Subobject.mk (kernelMapAlong E g hg) = kernelSubobject (bundleOverQuotient E g hg).q := by
  rw [bundleOverQuotient_q_eq]
  exact mk_eq_kernelSubobject_of_shortExact (shortExact_kernelMapAlong E g hg)

/-- **The first layer**: a morphism `T ⟶ 𝐏(ℰ)` over `f` is the same datum as a subobject of
`f^*ℰ` with cokernel of rank one, namely the image of `g^*ℰ' ⟶ f^*ℰ`. -/
def bundleSubEquiv (f : T ⟶ X) :
    { g : T ⟶ bundle E // g ≫ bundleProj E = f } ≃
      { S : Subobject ((Scheme.Modules.pullback f).obj E) //
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          (cokernel S.arrow) 1 } :=
  (bundleOverEquiv E f).trans (invertibleQuotientClassEquiv _)

/-- The subobject of `f^*ℰ` attached to `g : T ⟶ 𝐏(ℰ)` over `f` is the image of the kernel
inclusion along `g`. -/
theorem bundleSubEquiv_apply (f : T ⟶ X) (g : { g : T ⟶ bundle E // g ≫ bundleProj E = f }) :
    (bundleSubEquiv E f g).1 = Subobject.mk (kernelMapAlong E g.1 g.2) := by
  rw [mk_kernelMapAlong, bundleSubEquiv, Equiv.trans_apply, bundleOverEquiv_apply,
    invertibleQuotientClassEquiv_mk]
  rfl

/-- **The kernel inclusion along a composite** is the base change of the kernel inclusion
along the second factor, read through the comparisons of iterated pullbacks. -/
theorem kernelMapAlong_comp {T' : Scheme.{u}} (k : T' ⟶ T) (g : T ⟶ bundle E)
    (hg : g ≫ bundleProj E = f) (b : T' ⟶ bundle E) (hb : k ≫ g = b) (f' : T' ⟶ X)
    (hf' : k ≫ f = f') (hb' : b ≫ bundleProj E = f') :
    (Scheme.Modules.pullbackComp k g).hom.app _ ≫ (Scheme.Modules.pullbackCongr hb).hom.app _ ≫
        kernelMapAlong E b hb' =
      (Scheme.Modules.pullback k).map (kernelMapAlong E g hg) ≫
        (Scheme.Modules.pullbackComp k f).hom.app E ≫
        (Scheme.Modules.pullbackCongr hf').hom.app E := by
  subst hb hf'
  have key := Stacks.Modules.pullbackComp_congr_assoc k g (bundleProj E) (k ≫ g) rfl f hg
    (k ≫ f) hb' E
  have n1 := (Scheme.Modules.pullbackComp k g).hom.naturality (kernel.ι (bundleTautological E))
  dsimp only [Functor.comp_map] at n1
  have hc : ∀ {Y Z : Scheme.{u}} {a : Y ⟶ Z} (M : Z.Modules) (h : a = a),
      (Scheme.Modules.pullbackCongr h).hom.app M = 𝟙 _ := by
    intros; simp [Scheme.Modules.pullbackCongr]
  rw [hc, hc]
  rw [hc, hc] at key
  simp only [kernelMapAlong, Functor.map_comp, Category.assoc, Category.id_comp,
    Category.comp_id] at key ⊢
  rw [← reassoc_of% n1, key]

end Kernel

/-! ### The tower -/

/-- **The tower of projective bundles of tautological kernels** `tower m ℰ`, with its
projection to `X`: `tower 0 ℰ = X`, and `tower (m + 1) ℰ` is the tower of length `m` over `𝐏(ℰ)`
built on the tautological kernel `ℰ'`, followed by `𝐏(ℰ) ⟶ X`. It is a composition of `m`
projective space bundles over `X`. -/
def tower : (m : ℕ) → {X : Scheme.{u}} → (E : X.Modules) →
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] →
    Σ Y : Scheme.{u}, Y ⟶ X
  | 0, X, _, _ => ⟨X, 𝟙 X⟩
  | m + 1, _, E, hE =>
    ⟨(@tower m _ (kernel (@bundleTautological _ E hE))
        (@isFiniteLocallyFree_kernel_bundleTautological _ E hE)).1,
      (@tower m _ (kernel (@bundleTautological _ E hE))
        (@isFiniteLocallyFree_kernel_bundleTautological _ E hE)).2 ≫ @bundleProj _ E hE⟩

/-- The part of the tower of length `m + 1` above its first layer `𝐏(ℰ)`: the tower of
length `m` over `𝐏(ℰ)` built on the tautological kernel. -/
abbrev kernelTower (m : ℕ) {X : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    Σ Y : Scheme.{u}, Y ⟶ bundle E :=
  @tower m _ (kernel (bundleTautological E)) (isFiniteLocallyFree_kernel_bundleTautological E)

/-- The tower of length `0` is `X` itself. -/
theorem tower_zero {X : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    tower 0 E = ⟨X, 𝟙 X⟩ :=
  rfl

/-- The tower of length `m + 1` is the tower of length `m` over `𝐏(ℰ)` built on the
tautological kernel, followed by `𝐏(ℰ) ⟶ X`. -/
theorem tower_succ (m : ℕ) {X : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    tower (m + 1) E = ⟨(kernelTower m E).1, (kernelTower m E).2 ≫ bundleProj E⟩ :=
  rfl

/-- Splitting a morphism into a composite: a morphism into `Y` over `f` through `Y ⟶ P ⟶ X` is
a morphism `T ⟶ P` over `f` together with a morphism `T ⟶ Y` over it. -/
def overCompEquiv {T Y P X : Scheme.{u}} (a : Y ⟶ P) (p : P ⟶ X) (f : T ⟶ X) :
    { g : T ⟶ Y // g ≫ a ≫ p = f } ≃ Σ g₁ : { g₁ : T ⟶ P // g₁ ≫ p = f },
      { g : T ⟶ Y // g ≫ a = g₁.1 } where
  toFun g := ⟨⟨g.1 ≫ a, by rw [Category.assoc, g.2]⟩, ⟨g.1, rfl⟩⟩
  invFun x := ⟨x.2.1, by rw [← Category.assoc, x.2.2, x.1.2]⟩
  left_inv g := rfl
  right_inv x := Sigma.subtype_ext (Subtype.ext x.2.2) rfl

section Step

variable {X T : Scheme.{u}} (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (f : T ⟶ X) (m : ℕ)

/-- **The step of the induction**: a morphism `g₁ : T ⟶ 𝐏(ℰ)` over `f` together with a flag of
length `m` of `g₁^*ℰ'` is a flag of length `m + 1` of `f^*ℰ`, by prepending the kernel of the
quotient `g₁` classifies. -/
def consSigmaEquiv :
    (Σ g₁ : { g : T ⟶ bundle E // g ≫ bundleProj E = f },
      Flag ((Scheme.Modules.pullback g₁.1).obj (kernel (bundleTautological E))) m) ≃
      Flag ((Scheme.Modules.pullback f).obj E) (m + 1) :=
  Equiv.ofBijective
    (fun x => Flag.cons (kernelMapAlong E x.1.1 x.1.2)
      (rank_cokernel_kernelMapAlong E x.1.1 x.1.2) x.2)
    ⟨by
      rintro ⟨g₁, F⟩ ⟨g₁', F'⟩ h
      have h0 := congrArg (fun G : Flag _ (m + 1) => G.sub 0) h
      simp only [Flag.cons_sub_zero] at h0
      have hg : g₁ = g₁' := (bundleSubEquiv E f).injective (Subtype.ext (by
        rw [bundleSubEquiv_apply, bundleSubEquiv_apply, h0]))
      subst hg
      exact Sigma.ext rfl (heq_of_eq ((Flag.consEquiv _
        (rank_cokernel_kernelMapAlong E g₁.1 g₁.2) m).injective (Subtype.ext h))),
    by
      intro G
      obtain ⟨g₁, hg₁⟩ := (bundleSubEquiv E f).surjective ⟨G.sub 0, G.rank 0⟩
      have h0 : G.sub 0 = Subobject.mk (kernelMapAlong E g₁.1 g₁.2) := by
        rw [← bundleSubEquiv_apply, hg₁]
      refine ⟨⟨g₁, Flag.tail _ (rank_cokernel_kernelMapAlong E g₁.1 g₁.2) G h0⟩, ?_⟩
      exact congrArg Subtype.val ((Flag.consEquiv _ (rank_cokernel_kernelMapAlong E g₁.1 g₁.2)
        m).apply_symm_apply ⟨G, h0⟩)⟩

/-- The step of the induction prepends the kernel of the quotient that `g₁` classifies. -/
@[simp]
theorem consSigmaEquiv_apply
    (x : Σ g₁ : { g : T ⟶ bundle E // g ≫ bundleProj E = f },
      Flag ((Scheme.Modules.pullback g₁.1).obj (kernel (bundleTautological E))) m) :
    consSigmaEquiv E f m x =
      Flag.cons (kernelMapAlong E x.1.1 x.1.2) (rank_cokernel_kernelMapAlong E x.1.1 x.1.2) x.2 :=
  rfl

/-- The step of the induction, assembled: given the functor of points of the tower over
`𝐏(ℰ)`, the morphisms into the tower of length `m + 1` over `f` are the flags of length `m + 1`
of `f^*ℰ`. -/
def towerSuccEquiv
    (e : ∀ {T' : Scheme.{u}} (g₁ : T' ⟶ bundle E),
      { g : T' ⟶ (kernelTower m E).1 // g ≫ (kernelTower m E).2 = g₁ } ≃
        Flag ((Scheme.Modules.pullback g₁).obj (kernel (bundleTautological E))) m) :
    { g : T ⟶ (tower (m + 1) E).1 // g ≫ (tower (m + 1) E).2 = f } ≃
      Flag ((Scheme.Modules.pullback f).obj E) (m + 1) :=
  let e1 := overCompEquiv (Y := (kernelTower m E).1) (P := bundle E) (kernelTower m E).2
      (bundleProj E) f
  let e2 : (Σ g₁ : { g₁ : T ⟶ bundle E // g₁ ≫ bundleProj E = f },
      { g : T ⟶ (kernelTower m E).1 // g ≫ (kernelTower m E).2 = g₁.1 }) ≃
      (Σ g₁ : { g₁ : T ⟶ bundle E // g₁ ≫ bundleProj E = f },
        Flag ((Scheme.Modules.pullback g₁.1).obj (kernel (bundleTautological E))) m) :=
    Equiv.sigmaCongrRight fun g₁ => e g₁.1
  let e3 := consSigmaEquiv E f m
  let e12 := e1.trans e2
  e12.trans e3

end Step

/-- **The functor of points of the tower**: for a scheme `f : T ⟶ X` over `X`, the morphisms
`T ⟶ tower m ℰ` over `X` are the flags of length `m` of `f^*ℰ`. -/
def towerEquiv : (m : ℕ) → {X : Scheme.{u}} → (E : X.Modules) →
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] → {T : Scheme.{u}} →
    (f : T ⟶ X) →
    { g : T ⟶ (tower m E).1 // g ≫ (tower m E).2 = f } ≃
      Flag ((Scheme.Modules.pullback f).obj E) m
  | 0, _, _, _, _, f =>
    @Equiv.ofUnique _ _
      { default := ⟨f, Category.comp_id f⟩
        uniq := fun g => Subtype.ext ((Category.comp_id g.1).symm.trans g.2) } inferInstance
  | m + 1, _, E, hE, _, f =>
    @towerSuccEquiv _ _ E hE f m fun g₁ =>
      @towerEquiv m _ (kernel (@bundleTautological _ E hE))
        (@isFiniteLocallyFree_kernel_bundleTautological _ E hE) _ g₁

/-- **The flag of a morphism into the tower of length `m + 1`**: the kernel of the quotient
its first layer classifies, followed by the flag that the rest of the tower assigns. -/
theorem towerEquiv_succ_apply (m : ℕ) {X : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] {T : Scheme.{u}}
    (f : T ⟶ X) (g : { g : T ⟶ (tower (m + 1) E).1 // g ≫ (tower (m + 1) E).2 = f }) :
    towerEquiv (m + 1) E f g =
      Flag.cons (kernelMapAlong E (g.1 ≫ (kernelTower m E).2)
          ((Category.assoc _ _ _).trans g.2))
        (rank_cokernel_kernelMapAlong E _ _)
        (@towerEquiv m _ (kernel (bundleTautological E))
          (isFiniteLocallyFree_kernel_bundleTautological E) _
          (g.1 ≫ (kernelTower m E).2) ⟨g.1, rfl⟩) :=
  rfl

/-- **The functor of points of the tower is natural in the test scheme**: for `k : T' ⟶ T`, the
flag of `k ≫ g` is the base change along `k` of the flag of `g`, the pullback of `f^*ℰ` along
`k` being identified with `f'^*ℰ` (`f' = k ≫ f`) by the comparison of iterated pullbacks. -/
theorem towerEquiv_comp (m : ℕ) {X : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] {T T' : Scheme.{u}}
    (k : T' ⟶ T) (f : T ⟶ X) (g : { g : T ⟶ (tower m E).1 // g ≫ (tower m E).2 = f })
    (f' : T' ⟶ X) (hf' : k ≫ f = f') :
    towerEquiv m E f' ⟨k ≫ g.1, by rw [Category.assoc, g.2, hf']⟩ =
      Flag.pullback k (((Scheme.Modules.pullbackComp k f).app E ≪≫
        (Scheme.Modules.pullbackCongr hf').app E).symm) (towerEquiv m E f g) := by
  induction m generalizing X T T' with
  | zero => exact Subsingleton.elim _ _
  | succ m ih =>
    rw [towerEquiv_succ_apply, towerEquiv_succ_apply]
    set g₁ := g.1 ≫ (kernelTower m E).2 with hg₁
    have hg₁f : g₁ ≫ bundleProj E = f := (Category.assoc _ _ _).trans g.2
    have hc : k ≫ g₁ = (k ≫ g.1) ≫ (kernelTower m E).2 := (Category.assoc _ _ _).symm
    have hb' : ((k ≫ g.1) ≫ (kernelTower m E).2) ≫ bundleProj E = f' :=
      (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
        ((congrArg (fun t => k ≫ t) hg₁f).trans hf'))
    have hcoh := kernelMapAlong_comp E k g₁ hg₁f _ hc f' hf' hb'
    have hih := @ih _ (kernel (bundleTautological E))
      (isFiniteLocallyFree_kernel_bundleTautological E) _ _ k g₁ ⟨g.1, rfl⟩ _ hc
    refine Flag.ext (funext fun i => ?_)
    refine Fin.cases ?_ (fun i => ?_) i
    · have := mono_kernelMapAlong E g₁ hg₁f
      have := mono_pullback_map_arrow k (Subobject.mk (kernelMapAlong E g₁ hg₁f)) 1
        ((rank_cokernel_mk_iff _ 1).mpr (rank_cokernel_kernelMapAlong E g₁ hg₁f))
      show Subobject.mk (kernelMapAlong E ((k ≫ g.1) ≫ (kernelTower m E).2) hb') =
        Subobject.mk ((Scheme.Modules.pullback k).map
            (Subobject.mk (kernelMapAlong E g₁ hg₁f)).arrow ≫
          ((Scheme.Modules.pullbackComp k f).app E ≪≫
            (Scheme.Modules.pullbackCongr hf').app E).symm.inv)
      refine Subobject.mk_eq_mk_of_comm _ _
        (((Scheme.Modules.pullbackComp k g₁).app _ ≪≫
          (Scheme.Modules.pullbackCongr hc).app _).symm ≪≫
          (Scheme.Modules.pullback k).mapIso (Subobject.underlyingIso _).symm) ?_
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom,
        Category.assoc, Iso.trans_inv, Iso.symm_inv]
      rw [← Functor.map_comp_assoc, Subobject.underlyingIso_arrow, ← hcoh]
      simp
    · set F := @towerEquiv m _ (kernel (bundleTautological E))
        (isFiniteLocallyFree_kernel_bundleTautological E) _ g₁ ⟨g.1, rfl⟩ with hF
      have := mono_kernelMapAlong E g₁ hg₁f
      have := mono_kernelMapAlong E _ hb'
      have := mono_pullback_map_arrow k (F.sub i) _ (F.rank i)
      have := mono_pullback_map_arrow k ((Subobject.map (kernelMapAlong E g₁ hg₁f)).obj (F.sub i))
        _ (Flag.rank_map _ (rank_cokernel_kernelMapAlong E g₁ hg₁f) F i)
      show (Subobject.map (kernelMapAlong E _ hb')).obj
          ((@towerEquiv m _ (kernel (bundleTautological E))
            (isFiniteLocallyFree_kernel_bundleTautological E) _ ((k ≫ g.1) ≫ (kernelTower m E).2)
            ⟨k ≫ g.1, rfl⟩).sub i) =
        Subobject.mk ((Scheme.Modules.pullback k).map
            ((Subobject.map (kernelMapAlong E g₁ hg₁f)).obj (F.sub i)).arrow ≫
          ((Scheme.Modules.pullbackComp k f).app E ≪≫
            (Scheme.Modules.pullbackCongr hf').app E).symm.inv)
      rw [hih]
      show (Subobject.map (kernelMapAlong E _ hb')).obj (Subobject.mk
          ((Scheme.Modules.pullback k).map (F.sub i).arrow ≫
            ((Scheme.Modules.pullbackComp k g₁).app _ ≪≫
              (Scheme.Modules.pullbackCongr hc).app _).symm.inv)) = _
      rw [Subobject.map_mk]
      refine Subobject.mk_eq_mk_of_comm _ _
        ((Scheme.Modules.pullback k).mapIso (Flag.mapIso _ (F.sub i)).symm) ?_
      simp only [Functor.mapIso_hom, Iso.symm_hom, Flag.map_arrow, Functor.map_comp,
        Category.assoc, Iso.symm_inv, Iso.trans_hom, Iso.app_hom]
      rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
        Category.id_comp, hcoh]

end Stacks.FlagTower

end
