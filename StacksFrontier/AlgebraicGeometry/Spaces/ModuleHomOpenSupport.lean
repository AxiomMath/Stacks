module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFpqcDescentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse

/-!
# Homomorphisms into a module supported in an open subspace

Let `k : W' ⟶ W` be an open immersion of algebraic spaces and `A`, `Bb` two quasi-coherent
`𝒪_W`-modules, `Bb` of finite type with support contained in the image of `|W'|`.  Then pulling
back along `k` is a bijection

`Hom_{𝒪_W}(A, Bb) ≃ Hom_{𝒪_{W'}}(k^*A, k^*Bb)`.

Indeed `W'` and the open subspace `V` on the complement of the support of `Bb` form a Zariski
covering of `W`, on `V` the module `Bb` vanishes, and homomorphisms of quasi-coherent modules
glue along fpqc coverings (Stacks 04W8): a homomorphism on `W'` together with the zero
homomorphism on `V` agree on the overlap, the target vanishing there.

## Main results

* `AlgebraicGeometry.Space.bijective_modulePullback_map_of_supportOfSheaf_subset_range`: pulling
  back along an open immersion whose image contains the support of the target is a bijection on
  homomorphisms.

## References

* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 08JY](https://stacks.math.columbia.edu/tag/08JY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

open QuasiCoherentDescent

/-- Along equal morphisms the canonical comparison of two iterated inverse images is compatible
with the inverse images of a morphism of modules. -/
theorem modulePullback_map_comp_canonicalComparison_of_eq {A P Q : AlgebraicSpaces B S hS}
    {a b : P ⟶ Q} (hab : a = b) (fi : Q ⟶ A) (h : a ≫ fi = b ≫ fi)
    {M N : Modules.{u, u} B S hS Q.1 Q.2} {M' N' : Modules.{u, u} B S hS A.1 A.2}
    (_eM : M = (modulePullback B S hS fi).obj M') (_eN : N = (modulePullback B S hS fi).obj N')
    (γ : (modulePullback B S hS fi).obj M' ⟶ (modulePullback B S hS fi).obj N') :
    (modulePullback B S hS a).map γ ≫ (canonicalComparison a b fi fi h N').hom =
      (canonicalComparison a b fi fi h M').hom ≫ (modulePullback B S hS b).map γ := by
  subst hab
  simp [canonicalComparison]

/-- **Gluing along a two-member covering on which the target vanishes on one member.**  Let
`c` be an fpqc covering of `W` by two algebraic spaces, the member `c true` a monomorphism, and
`Bb` a quasi-coherent module whose pullback to `c false` vanishes.  Then pulling back along
`c true` is a bijection `Hom(A, Bb) ≃ Hom((c true)^*A, (c true)^*Bb)`. -/
theorem bijective_modulePullback_map_of_isFpqcCovering_of_isZero
    {W : AlgebraicSpaces B S hS} (Zi : Bool → AlgebraicSpaces B S hS) (c : ∀ i, Zi i ⟶ W)
    (hcov : IsFpqcCovering B S hS fun i => (c i).hom) (hmono : Mono (c true))
    (A Bb : Modules.{u, u} B S hS W.1 W.2)
    (hA : A.IsQuasicoherentOnSite) (hB : Bb.IsQuasicoherentOnSite)
    (hzero : IsZero ((modulePullback B S hS (c false)).obj Bb)) :
    Function.Bijective (fun α : A ⟶ Bb ↦ (modulePullback B S hS (c true)).map α) := by
  have hzeroPull : ∀ {P : AlgebraicSpaces B S hS} (a : P ⟶ Zi false),
      IsZero ((modulePullback B S hS a).obj ((modulePullback B S hS (c false)).obj Bb)) :=
    fun a => Functor.map_isZero _ hzero
  refine ⟨fun α β hαβ => ?_, fun γ => ?_⟩
  · refine modulePullback_map_injective_of_isFpqcCovering B S hS
      (reprFpqcHomInjective.{u, 0} B S hS) Zi c hcov α β fun i => ?_
    cases i
    · exact hzero.eq_of_tgt _ _
    · exact hαβ
  · let w : ∀ i, (modulePullback B S hS (c i)).obj A ⟶ (modulePullback B S hS (c i)).obj Bb :=
      fun i => Bool.casesOn (motive := fun i =>
        (modulePullback B S hS (c i)).obj A ⟶ (modulePullback B S hS (c i)).obj Bb) i 0 γ
    have hw : IsPairwiseCompatible B S hS Zi c w := by
      intro i j
      cases i <;> cases j
      · exact (hzeroPull (pairSnd B S hS Zi c false false)).eq_of_tgt _ _
      · exact (IsZero.of_iso (hzeroPull (pairFst B S hS Zi c false true))
          (canonicalComparison (pairFst B S hS Zi c false true) (pairSnd B S hS Zi c false true)
            (c false) (c true) (pair_condition B S hS Zi c false true) Bb).symm).eq_of_tgt _ _
      · exact (hzeroPull (pairSnd B S hS Zi c true false)).eq_of_tgt _ _
      · have hfs : pairFst B S hS Zi c true true = pairSnd B S hS Zi c true true :=
          (cancel_mono (c true)).1 (pair_condition B S hS Zi c true true)
        exact modulePullback_map_comp_canonicalComparison_of_eq hfs (c true)
          (pair_condition B S hS Zi c true true) rfl rfl γ
    obtain ⟨φ, hφ, -⟩ := existsUnique_modulePullback_map_eq Zi c hcov hA hB w hw
    exact ⟨φ, hφ true⟩

/-- **Gluing along a Zariski covering by two open subspaces, on one of which the target
vanishes.**  Let `k : W' ⟶ W` and `v : V ⟶ W` be open immersions whose images cover the points of
`W`, and `A`, `Bb` quasi-coherent `𝒪_W`-modules with `v^*Bb = 0`.  Then pulling back along `k` is
a bijection `Hom(A, Bb) ≃ Hom(k^*A, k^*Bb)`. -/
theorem bijective_modulePullback_map_of_isOpenImmersion_of_isZero
    {W W' V : AlgebraicSpaces B S hS} (k : W' ⟶ W) (v : V ⟶ W)
    (hk : IsOpenImmersion B S hS k.hom) (hv : IsOpenImmersion B S hS v.hom)
    (hjs : ∀ x : points B S hS W.1, x ∈ Set.range (pointsMap B S hS W'.1 k.hom) ∨
      x ∈ Set.range (pointsMap B S hS V.1 v.hom))
    (A Bb : Modules.{u, u} B S hS W.1 W.2)
    (hA : A.IsQuasicoherentOnSite) (hB : Bb.IsQuasicoherentOnSite)
    (hzero : IsZero ((modulePullback B S hS v).obj Bb)) :
    Function.Bijective (fun α : A ⟶ Bb ↦ (modulePullback B S hS k).map α) := by
  have hcov : IsFpqcCovering B S hS fun b =>
      (Bool.casesOn (motive := fun b => Bool.casesOn b V W' ⟶ W) b v k).hom := by
    refine isFpqcCovering_of_isZariskiCovering B S hS (fun b => (Bool.casesOn b V W' :
        AlgebraicSpaces B S hS).1) _ W.property (fun b => (Bool.casesOn b V W' :
        AlgebraicSpaces B S hS).property) ⟨fun b => ?_, fun x => ?_⟩
    · cases b
      · exact hv
      · exact hk
    · rcases hjs x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨true, y, hy⟩
      · exact ⟨false, y, hy⟩
  have : Mono k.hom := mono_of_isOpenImmersion B S hS _ hk
  have hmono : Mono k := ⟨fun g h hgh => ObjectProperty.hom_ext _
    ((cancel_mono k.hom).1 (congrArg InducedCategory.Hom.hom hgh))⟩
  have h := bijective_modulePullback_map_of_isFpqcCovering_of_isZero
    (fun b => Bool.casesOn b V W') (fun b => Bool.casesOn (motive := fun b =>
      Bool.casesOn b V W' ⟶ W) b v k) hcov hmono A Bb hA hB (by dsimp only; exact hzero)
  dsimp only at h
  exact h

/-- **Pulling homomorphisms back to an open subspace containing the support of the target is a
bijection.**  For an open immersion `k : W' ⟶ W` and quasi-coherent `𝒪_W`-modules `A` and `Bb`,
`Bb` of finite type with support in the image of `|W'|`, the map `α ↦ k^*α` is a bijection
`Hom(A, Bb) ≃ Hom(k^*A, k^*Bb)`. -/
theorem bijective_modulePullback_map_of_supportOfSheaf_subset_range {W W' : AlgebraicSpaces B S hS}
    (k : W' ⟶ W) (hk : IsOpenImmersion B S hS k.hom) (A Bb : Modules.{u, u} B S hS W.1 W.2)
    (hA : A.IsQuasicoherentOnSite) (hB : Bb.IsQuasicoherentOnSite)
    (hBft : SheafOfModules.IsFiniteTypeOnSite Bb)
    (hsupp : supportOfSheaf B S hS W.1 ((SheafOfModules.toSheaf _).obj Bb) ⊆
      Set.range (pointsMap B S hS W'.1 k.hom)) :
    Function.Bijective (fun α : A ⟶ Bb ↦ (modulePullback B S hS k).map α) := by
  have hZ : IsClosed (supportOfSheaf B S hS W.1 ((SheafOfModules.toSheaf _).obj Bb)) :=
    have := hBft
    isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS W.1 W.property Bb
  obtain ⟨V, v, hv, hvrange⟩ : ∃ (V : AlgebraicSpaces B S hS) (v : V ⟶ W),
      IsOpenImmersion B S hS v.hom ∧ Set.range (pointsMap B S hS V.1 v.hom) =
        (supportOfSheaf B S hS W.1 ((SheafOfModules.toSheaf _).obj Bb))ᶜ := by
    have hVos := isOpenSubspace_openSubspaceOfPoints B S hS W.property _ hZ.isOpen_compl
    exact ⟨⟨_, hVos.1⟩, ObjectProperty.homMk _, hVos.2,
      range_pointsMap_ι_openSubspaceOfPoints B S hS _⟩
  have hvzero : IsZero ((modulePullback B S hS v).obj Bb) := by
    refine isZero_of_supportOfSheaf_eq_empty B S hS V _ ?_
    rw [supportOfSheaf_modulePullback_of_isEtale B S hS v (isEtale_of_isOpenImmersion B S hS hv)
      Bb, Set.eq_empty_iff_forall_notMem]
    intro y hy
    exact (hvrange ▸ Set.mem_range_self y :
      pointsMap B S hS V.1 v.hom y ∈ (supportOfSheaf B S hS W.1
        ((SheafOfModules.toSheaf _).obj Bb))ᶜ) hy
  refine bijective_modulePullback_map_of_isOpenImmersion_of_isZero k v hk hv (fun x => ?_)
    A Bb hA hB hvzero
  by_cases hx : x ∈ supportOfSheaf B S hS W.1 ((SheafOfModules.toSheaf _).obj Bb)
  · exact Or.inl (hsupp hx)
  · exact Or.inr (hvrange ▸ hx)

end AlgebraicGeometry.Space

end
