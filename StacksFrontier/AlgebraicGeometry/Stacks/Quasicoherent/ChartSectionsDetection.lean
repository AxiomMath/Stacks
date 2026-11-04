module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineSpanDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.EtaleAffineCovering
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit

/-!
# Quasi-coherent modules are detected on the sections over a smooth chart

Let `a : (Sch/U) ⟶ 𝒳` be a smooth surjective 1-morphism to an algebraic stack and `u = a(id_U)`
the object it names.  Every object of `𝒳` is covered, for the fppf topology, by objects over
affine schemes with an arrow to `u` (Stacks 06XH); a quasi-coherent module is cartesian between
affine objects (Stacks 03DX).  Hence, when `U` is affine:

* a morphism out of a quasi-coherent module vanishing on the sections over `u` vanishes;
* an epimorphism of quasi-coherent modules is surjective on the sections over every object over
  an affine scheme.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.chartSieve_mem`
* `AlgebraicGeometry.Stack.AlgebraicStacks.hom_eq_zero_of_chart`
* `AlgebraicGeometry.Stack.AlgebraicStacks.surjective_app_of_epi`

## References

* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.FibredSite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {U : BigFppfOver B S hS}
  (a : schemeStack.{u, w} B S hS U ⟶ 𝒳)

attribute [local instance] objModule

/-- The object of `𝒳` named by a 1-morphism `a : (Sch/U) ⟶ 𝒳`. -/
abbrev chartObject : 𝒳.val.val.obj :=
  (CatFiberedInGroupoids.homFunctor a.hom).obj (Over.mk (𝟙 U))

/-- The sieve of arrows out of objects admitting an arrow to `a(id_U)`. -/
def chartSieve (y : 𝒳.val.val.obj) : Sieve y where
  arrows {z} _ := Nonempty (z ⟶ chartObject a)
  downward_closed := by
    rintro z z' k ⟨d⟩ g
    exact ⟨g ≫ d⟩

/-- **The objects mapping to a smooth surjective chart cover**, Stacks 06XH. -/
theorem chartSieve_mem (hsm : AlgebraicStacks.IsSmooth B S hS a) (hsurj : IsSurjective B S hS a)
    (y : 𝒳.val.val.obj) :
    chartSieve a y ∈ BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf y := by
  obtain ⟨x', α, hgen⟩ := exists_etaleLocalLift B S hS a hsurj hsm y
  refine (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf).superset_covering ?_
    (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale y hgen)
  rintro z _ ⟨z', h, k, hk, rfl⟩
  cases hk
  exact ⟨h ≫ (CatFiberedInGroupoids.homFunctor a.hom).map (Over.mkIdTerminal.from x')⟩

variable {a}

/-- **A section vanishing on the members over affine schemes of the chart sieve vanishes.** -/
theorem eq_zero_of_chart (hsm : AlgebraicStacks.IsSmooth B S hS a)
    (hsurj : IsSurjective B S hS a)
    (N : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)) {y : 𝒳.val.val.obj} (t : N.val.obj (op y))
    (ht : ∀ ⦃z : 𝒳.val.val.obj⦄ (k : z ⟶ y), IsAffineOver B S hS (𝒳.val.val.p.obj z) →
      Nonempty (z ⟶ chartObject a) → N.val.restrictₛₗ k.op t = 0) : t = 0 := by
  let R := FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero (R := R) t
    (chartSieve_mem a hsm hsurj y) ?_
  intro z k ⟨d⟩
  let T : Sieve z :=
    { arrows := fun {V} k' => N.val.restrictₛₗ k'.op (N.val.restrictₛₗ k.op t) = 0
      downward_closed := fun {V V'} k' hk' g => by
        rw [restrictₛₗ_comp_apply, hk', map_zero] }
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero (R := R) _
    (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale z
      (mem_etale_of_forall_isAffine B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids z T
        fun {V} k' hV => ?_)) fun _ _ h => h
  show N.val.restrictₛₗ k'.op (N.val.restrictₛₗ k.op t) = 0
  rw [← restrictₛₗ_comp_apply]
  exact ht (k' ≫ k) hV ⟨k' ≫ d⟩

/-- A morphism of modules sends the span of the restrictions along `d : z ⟶ u` into a submodule
`P` as soon as it sends the restrictions themselves into `P`. -/
private theorem app_mem_of_mem_span_range_restrictₛₗ
    {M N : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)} (f : M ⟶ N) {u' z : 𝒳.val.val.obj} (d : z ⟶ u')
    (P : Submodule (objRing B S hS 𝒳.val.val.p z) (N.val.obj (op z)))
    (hP : ∀ m, f.val.app (op z) (M.val.restrictₛₗ d.op m) ∈ P) {t : M.val.obj (op z)}
    (ht : t ∈ Submodule.span (objRing B S hS 𝒳.val.val.p z) (Set.range (M.val.restrictₛₗ d.op))) :
    f.val.app (op z) t ∈ P := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨m, rfl⟩
    exact hP m
  · rw [map_zero]; exact zero_mem _
  · intro x x' _ _ hx hx'; rw [map_add]; exact add_mem hx hx'
  · intro c x _ hx
    rw [show f.val.app (op z) (c • x) = c • f.val.app (op z) x from
      (f.val.app (op z)).hom.map_smul c x]
    exact Submodule.smul_mem _ _ hx

/-- **A morphism out of a quasi-coherent module vanishing over the chart vanishes**, when the
chart lies over an affine scheme. -/
theorem hom_eq_zero_of_chart (hsm : AlgebraicStacks.IsSmooth B S hS a)
    (hsurj : IsSurjective B S hS a)
    (hu : IsAffineOver B S hS (𝒳.val.val.p.obj (chartObject a)))
    {M N : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)} (hM : M.IsQuasicoherentOnSite) (f : M ⟶ N)
    (hf : ∀ m, f.val.app (op (chartObject a)) m = 0) : f = 0 := by
  have key : ∀ (y : 𝒳.val.val.obj) (m : M.val.obj (op y)), f.val.app (op y) m = 0 := by
    intro y m
    refine eq_zero_of_chart hsm hsurj N _ fun z k hz ⟨d⟩ => ?_
    have hnat : N.val.restrictₛₗ k.op (f.val.app (op y) m) =
        f.val.app (op z) (M.val.restrictₛₗ k.op m) :=
      (PresheafOfModules.naturality_apply f.val k.op m).symm
    rw [hnat]
    refine (Submodule.mem_bot _).1 (app_mem_of_mem_span_range_restrictₛₗ f d ⊥ (fun m' => ?_)
      (mem_span_range_restrictₛₗ M hM d hu hz (M.val.restrictₛₗ k.op m)))
    rw [Submodule.mem_bot]
    exact (PresheafOfModules.naturality_apply f.val d.op m').trans (by rw [hf]; exact map_zero _)
  ext y m
  exact key y.unop m

variable (𝒳) in
/-- **An epimorphism of quasi-coherent modules is surjective over affine objects.**  It is
locally surjective, and the image over an affine object descends (Stacks 023M), the sections over
a smaller affine object being spanned by restrictions (Stacks 03DX). -/
theorem surjective_app_of_epi
    {M N : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (π : M ⟶ N) [Epi π] {y : 𝒳.val.val.obj}
    (hy : IsAffineOver B S hS (𝒳.val.val.p.obj y)) :
    Function.Surjective (π.val.app (op y)) := by
  let : HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
      AddCommGrpCat.{u} := hasSheafifyEssentiallySmallSite _ _
  let : (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf).WEqualsLocallyBijective
      AddCommGrpCat.{u} := GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  intro x
  let Nr : Submodule (objRing B S hS 𝒳.val.val.p y) (N.val.obj (op y)) :=
    { carrier := Set.range (π.val.app (op y))
      add_mem' := by
        rintro _ _ ⟨m, rfl⟩ ⟨m', rfl⟩
        exact ⟨m + m', map_add _ m m'⟩
      zero_mem' := ⟨0, map_zero _⟩
      smul_mem' := by
        rintro c _ ⟨m, rfl⟩
        exact ⟨c • m, (π.val.app (op y)).hom.map_smul c m⟩ }
  suffices h : x ∈ Nr from h
  obtain ⟨T, hT, hloc⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi π x
  refine mem_of_forall_mem_restrictedSpan N hN hy Nr hT fun z g hg hz => ?_
  obtain ⟨t, ht⟩ := hloc g hg
  change π.val.app (op z) t = N.val.restrictₛₗ g.op x at ht
  rw [← ht]
  refine app_mem_of_mem_span_range_restrictₛₗ π g _ (fun m => ?_)
    (mem_span_range_restrictₛₗ M hM g hy hz t)
  exact (PresheafOfModules.naturality_apply π.val g.op m).symm ▸
    map_mem_restrictedSpan N g (show π.val.app (op y) m ∈ Nr from ⟨m, rfl⟩)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
