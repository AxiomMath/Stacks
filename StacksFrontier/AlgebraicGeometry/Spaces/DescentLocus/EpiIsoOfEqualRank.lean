module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeRankOpenSubspace
public import StacksFrontier.Topology.Sheaves.Modules.TensorAndDuals.EpiOfConstantRank
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Surjections between finite locally free modules of the same rank on a site

Let `R` be a sheaf of rings on a site whose rings of sections are commutative, and let
`f : M ⟶ N` be an epimorphism between two sheaves of `R`-modules which are both finite locally
free of the same rank `r`. Then `f` is an isomorphism. This is Stacks 089Q on an arbitrary site.

The argument is the one of the source. Over an object `W` lying over a trivializing object of
both `M` and `N`, the sections of both are free of rank `r` over `R(W)`, compatibly with
restriction. Epimorphisms are locally surjective, so the `r` basis sections of `N(W)` lift
after passing to a covering of `W`; over a member of that covering `f` is surjective on
sections, hence injective, because a surjective endomorphism of a finite free module over a
commutative ring is injective. Hence `f` is locally injective, and a locally injective and
locally surjective morphism of sheaves is an isomorphism.

## Main results

* `AlgebraicGeometry.SheafOfModules.iInf_mem_of_finite`: a finite intersection of covering
  sieves is a covering sieve.
* `AlgebraicGeometry.SheafOfModules.exists_sectionsLinearEquiv_of_isIso_π`: the sections of a
  module freely generated over an object by `n` sections are, over every object above it,
  naturally the `n`-tuples of sections of the structure sheaf.
* `AlgebraicGeometry.SheafOfModules.isIso_of_epi_of_isFiniteLocallyFreeOfIntRank`: the
  statement above.

## Implementation notes

The ringed-space form `Stacks.SheafOfModules.isIso_iff_epi_of_isFiniteLocallyFreeOfRank` is
proved for the site of open sets of a ringed space, through bases of sections that are
available only for a site whose objects and morphisms share a universe. The small étale site
of an algebraic space is not of that shape, so the sections are computed here with
`Stacks.SheafOfModules.exists_piEquiv_of_isColimit_cofan`, which has no universe constraint.
Commutativity of the rings of sections is a hypothesis, since the structure sheaves are
sheaves of `RingCat`.

## References

* [Stacks Project, Tag 089Q](https://stacks.math.columbia.edu/tag/089Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v u₁

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- A finite intersection of covering sieves is a covering sieve. -/
@[sga "4 II 1.1.1"]
theorem iInf_mem_of_finite {X : C} {ι : Type*} [Finite ι] (S : ι → Sieve X)
    (h : ∀ i, S i ∈ J X) : (⨅ i, S i) ∈ J X := by
  classical
  have := Fintype.ofFinite ι
  rw [← Finset.inf_univ_eq_iInf]
  exact Finset.inf_induction (J.top_mem X) (fun _ ha _ hb => J.intersection_covering ha hb)
    (fun i _ => h i)

/-- Over an object `W` with a trivialization `θ` of the sections of `N` over every object above
it, the restriction to a smaller object of the inverse image of a standard basis vector is the
inverse image of the same standard basis vector. -/
theorem map_symm_single_of_sectionsLinearEquiv {N : _root_.SheafOfModules.{u} R} {X₀ : C}
    {n : ℕ} (θ : ∀ (V : C) (_ : V ⟶ X₀),
        N.val.obj (op V) ≃ₗ[R.obj.obj (op V)] (Fin n → R.obj.obj (op V)))
    (hθ : ∀ (V : C) (a : V ⟶ X₀) (W : C) (b : W ⟶ V) (x : N.val.obj (op V)) (j : Fin n),
        θ W (b ≫ a) (N.val.map b.op x) j = R.obj.map b.op (θ V a x j))
    {V : C} (a : V ⟶ X₀) {W : C} (b : W ⟶ V) (j : Fin n) :
    N.val.map b.op ((θ V a).symm (Pi.single j 1)) = (θ W (b ≫ a)).symm (Pi.single j 1) := by
  classical
  apply (θ W (b ≫ a)).injective
  rw [LinearEquiv.apply_symm_apply]
  funext k
  rw [hθ, LinearEquiv.apply_symm_apply]
  by_cases hk : k = j
  · subst hk
    simp
  · simp [hk]

/-- Over an object whose ring of sections is commutative, a morphism of sheaves of modules whose
sections there are free of the same finite rank is injective on those sections as soon as it is
surjective on them. -/
private theorem injective_app_of_surjective_of_linearEquiv {W : C}
    (hcomm : ∀ a b : R.obj.obj (op W), a * b = b * a) {M N : _root_.SheafOfModules.{u} R}
    (f : M ⟶ N) {m n : ℕ}
    (θM : M.val.obj (op W) ≃ₗ[R.obj.obj (op W)] (Fin m → R.obj.obj (op W)))
    (θN : N.val.obj (op W) ≃ₗ[R.obj.obj (op W)] (Fin n → R.obj.obj (op W))) (hmn : m = n)
    (hs : Function.Surjective (f.val.app (op W))) : Function.Injective (f.val.app (op W)) := by
  let A := R.obj.obj (op W)
  let : CommRing A := { (inferInstance : Ring A) with mul_comm := hcomm }
  let eN : N.val.obj (op W) ≃ₗ[A] (Fin m → A) :=
    θN.trans (LinearEquiv.funCongrLeft A A (finCongr hmn))
  exact Stacks.SheafOfModules.injective_of_surjective_of_linearEquiv_fin
    (f.val.app (op W)).hom θM eN hs

variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Sections of a locally freely generated module.** If `σ` is a family of `n` sections of
`M` over `X₀` whose associated morphism from the free module is an isomorphism, then over every
object `V` with a morphism `a : V ⟶ X₀` the sections `M(V)` are the `n`-tuples of sections of
`R` over `V`, naturally in `(V, a)`. -/
theorem exists_sectionsLinearEquiv_of_isIso_π {M : _root_.SheafOfModules.{u} R} {X₀ : C}
    (σ : (M.over X₀).GeneratingSections) [hσ : IsIso σ.π] {n : ℕ} (e : σ.I ≃ Fin n) :
    ∃ θ : ∀ (V : C) (_ : V ⟶ X₀),
        M.val.obj (op V) ≃ₗ[R.obj.obj (op V)] (Fin n → R.obj.obj (op V)),
      ∀ (V : C) (a : V ⟶ X₀) (W : C) (b : W ⟶ V) (x : M.val.obj (op V)) (j : Fin n),
        θ W (b ≫ a) (M.val.map b.op x) j = R.obj.map b.op (θ V a x j) := by
  let c : Cofan (fun _ : Fin n => _root_.SheafOfModules.unit (R.over X₀)) :=
    Cofan.mk (M.over X₀) (fun j => _root_.SheafOfModules.ιFree (e.symm j) ≫ σ.π)
  have hc : IsColimit c :=
    ((Cofan.isColimitEquivOfEquiv e.symm _)
      (_root_.SheafOfModules.isColimitFreeCofan (R := R.over X₀) σ.I)).ofIsoColimit
      (Cofan.ext (@asIso _ _ _ _ σ.π hσ) fun _ => rfl)
  obtain ⟨θ, hθ⟩ := Stacks.SheafOfModules.exists_piEquiv_of_isColimit_cofan _ hc
  exact ⟨fun V a => θ (op (Over.mk a)), fun V a W b x j =>
    hθ (Over.homMk b : Over.mk (b ≫ a) ⟶ Over.mk a).op x j⟩

/-- Over each member of a local free presentation whose bases have cardinality `r`, the sections
of the module are naturally the `n`-tuples of sections of the structure sheaf, for some `n`
with `n = r`. -/
private theorem exists_sectionsLinearEquiv_of_isLocallyFreeData {M : _root_.SheafOfModules.{u} R}
    (q : _root_.SheafOfModules.LocalGeneratorsData.{u₁} M) (hq : q.IsLocallyFreeData) {r : ℤ}
    (hr : ∀ i, ∃ n : ℕ, (n : ℤ) = r ∧ Nonempty ((q.generators i).I ≃ Fin n)) (i : q.I) :
    ∃ (n : ℕ) (_ : (n : ℤ) = r) (θ : ∀ (V : C) (_ : V ⟶ q.X i),
        M.val.obj (op V) ≃ₗ[R.obj.obj (op V)] (Fin n → R.obj.obj (op V))),
      ∀ (V : C) (a : V ⟶ q.X i) (W : C) (b : W ⟶ V) (x : M.val.obj (op V)) (j : Fin n),
        θ W (b ≫ a) (M.val.map b.op x) j = R.obj.map b.op (θ V a x j) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hr i
  have := hq.isIso i
  obtain ⟨θ, hθ⟩ := exists_sectionsLinearEquiv_of_isIso_π (q.generators i) e
  exact ⟨n, hn, θ, hθ⟩

/-- A linear map into a module identified with `n`-tuples of scalars is surjective as soon as
its range contains the inverse images of the standard basis vectors. -/
theorem surjective_of_symm_single_mem_range {A : Type*} [Ring A] {P Q : Type*}
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q] {n : ℕ}
    (g : P →ₗ[A] Q) (θ : Q ≃ₗ[A] (Fin n → A))
    (h : ∀ j, θ.symm (Pi.single j 1) ∈ LinearMap.range g) : Function.Surjective g := by
  classical
  rw [← LinearMap.range_eq_top, eq_top_iff, ← ((Pi.basisFun A (Fin n)).map θ.symm).span_eq,
    Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  simpa using h j

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 089Q on a site.** Let `R` be a sheaf of rings on a site whose rings of sections are
commutative. An epimorphism between two sheaves of `R`-modules which are finite locally free of
the same rank is an isomorphism. -/
theorem isIso_of_epi_of_isFiniteLocallyFreeOfIntRank
    (hcomm : ∀ (X : Cᵒᵖ) (a b : R.obj.obj X), a * b = b * a)
    {M N : _root_.SheafOfModules.{u} R} {r : ℤ}
    (hM : IsFiniteLocallyFreeOfIntRank M r)
    (hN : IsFiniteLocallyFreeOfIntRank N r) (f : M ⟶ N) [Epi f] : IsIso f := by
  classical
  obtain ⟨qM, hqM, hrM⟩ := hM
  obtain ⟨qN, hqN, hrN⟩ := hN
  let φ := (PresheafOfModules.toPresheaf R.obj).map f.val
  have hloc : Presheaf.IsLocallySurjective J φ :=
    Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi f
  -- Trivializations of the sections over the members of the two coverings.
  choose nM hnM θM hθMnat using exists_sectionsLinearEquiv_of_isLocallyFreeData qM hqM hrM
  choose nN hnN θN hθNnat using exists_sectionsLinearEquiv_of_isLocallyFreeData qN hqN hrN
  -- The objects over which `f` is surjective on sections and which lie over both coverings.
  let P : C → Prop := fun W => ∃ (iM : qM.I) (_ : W ⟶ qM.X iM) (iN : qN.I) (_ : W ⟶ qN.X iN),
    Function.Surjective (f.val.app (op W))
  -- `P W'` holds once the basis vectors of `N` over `W` lift to `W'`.
  have hsurj : ∀ {W W' : C} {iM : qM.I} {iN : qN.I} (aM : W ⟶ qM.X iM) (aN : W ⟶ qN.X iN)
      (b : W' ⟶ W), (∀ j, ∃ t, f.val.app (op W') t =
        N.val.map b.op ((θN iN W aN).symm (Pi.single j 1))) → P W' :=
    fun {_ _ _ iN} aM aN b h => ⟨_, b ≫ aM, iN, b ≫ aN,
      surjective_of_symm_single_mem_range _ (θN iN _ (b ≫ aN)) fun j =>
        (h j).imp fun _ ht => ht.trans
          (map_symm_single_of_sectionsLinearEquiv _ (hθNnat iN) aN b j)⟩
  have hPdown : ∀ {W W' : C} (b : W' ⟶ W), P W → P W' := by
    rintro W W' b ⟨iM, aM, iN, aN, hs⟩
    exact hsurj aM aN b fun j => let ⟨t, ht⟩ := hs ((θN iN W aN).symm (Pi.single j 1))
      ⟨M.val.map b.op t, (PresheafOfModules.naturality_apply f.val b.op t).trans (congrArg _ ht)⟩
  -- Over such an object `f` is injective on sections.
  have hPinj : ∀ {W : C}, P W → Function.Injective (f.val.app (op W)) := by
    rintro W ⟨iM, aM, iN, aN, hs⟩
    exact injective_app_of_surjective_of_linearEquiv (hcomm (op W)) f (θM iM W aM) (θN iN W aN)
      (by exact_mod_cast (hnM iM).trans (hnN iN).symm) hs
  let Ssurj : ∀ T : C, Sieve T := fun T =>
    { arrows := fun W _ => P W
      downward_closed := fun h b => hPdown b h }
  -- The sieve `Ssurj T` covers every object `T`.
  have hcov : ∀ T : C, Ssurj T ∈ J T := by
    intro T
    have h₀ : Sieve.ofObjects qM.X T ⊓ Sieve.ofObjects qN.X T ∈ J T :=
      J.intersection_covering (qM.coversTop T) (qN.coversTop T)
    refine J.transitive h₀ _ fun W g hg => ?_
    obtain ⟨⟨iM, ⟨aM⟩⟩, ⟨iN, ⟨aN⟩⟩⟩ := hg
    let y : Fin (nN iN) → N.val.obj (op W) := fun j => (θN iN W aN).symm (Pi.single j 1)
    refine J.superset_covering ?_
      (iInf_mem_of_finite (fun j => Presheaf.imageSieve φ (y j))
        fun j => Presheaf.imageSieve_mem J φ (y j))
    intro W' b hb
    exact hsurj aM aN b fun j => (Sieve.sInf_apply b).1 hb _ ⟨j, rfl⟩
  have hlinj : Presheaf.IsLocallyInjective J φ := by
    refine ⟨fun {T} x x' hxx' => J.superset_covering ?_ (hcov T.unop)⟩
    intro W g hg
    apply hPinj hg
    exact (PresheafOfModules.naturality_apply f.val g.op x).trans
      ((congrArg _ hxx').trans (PresheafOfModules.naturality_apply f.val g.op x').symm)
  have : IsIso ((_root_.SheafOfModules.toSheaf R).map f) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨hlinj, hloc⟩
  exact isIso_of_reflects_iso f (_root_.SheafOfModules.toSheaf R)

end AlgebraicGeometry.SheafOfModules
