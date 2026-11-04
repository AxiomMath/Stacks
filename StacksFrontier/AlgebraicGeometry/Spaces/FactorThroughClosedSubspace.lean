module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Factoring a morphism of algebraic spaces through a closed subspace

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let
`Z ⊆ X` be a closed subspace with inclusion `i : Z ⟶ X`, and let `h : Y ⟶ X` be a morphism
of algebraic spaces.  Stacks 03MB asserts, for `𝓘 ⊆ 𝒪_X` the quasi-coherent ideal of `Z`,
that `h` factors through `i` exactly when `h^*𝓘 ⟶ h^*𝒪_X = 𝒪_Y` is zero.

The vanishing condition is written here in the form Stacks 03MB's own proof uses, namely
chartwise on the small étale site of `X`: for an étale scheme chart `U` of `X` the restriction
`𝓘|_U` is the ideal sheaf of the closed immersion of schemes `Z ×_X U ⟶ U`, which
`AlgebraicGeometry.Scheme.Hom.ker` names, and for a point of `Y` over an object `a` of the
site whose image in `X` factors through `U` by `k : a ⟶ U`, the vanishing of the pullback of
`𝓘` at that point is — by the adjunction between pullback and direct image, and because the
ideal is quasi-coherent — the inclusion of ideal sheaves on `U`

`(Z ×_X U ⟶ U).ker ≤ k.ker`.

That is the right-hand side of
`AlgebraicGeometry.Space.exists_comp_eq_iff_forall_ker_le`.  No pullback functor on modules
over an algebraic space is needed to state it, and
`AlgebraicGeometry.Space.mem_obj_iff_definingIdealAt_le` identifies it, on an *affine* chart,
with the inclusion of `AlgebraicGeometry.Space.definingIdealAt` into the kernel of pullback of
regular functions, so that the condition is one about the defining ideal of Stacks 03MB as the
library records it.

The proof follows Stacks 03MB.  A closed subspace is a *subfunctor* of `X`, so factoring
through it is the pointwise condition that every point of `Y` land in `Z`; no descent of
closed immersions along an étale chart is used anywhere.  The two ingredients are:

* a point of `X` over `a` which factors through a chart `U` by `k` lies in `Z` exactly when
  `k` factors through the closed immersion `Z ×_X U ⟶ U`
  (`AlgebraicGeometry.Space.mem_obj_iff_ker_le`), which is Mathlib's universal property
  `AlgebraicGeometry.IsClosedImmersion.lift` of closed immersions of schemes together with
  `AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq` to put the lift back in the site;
* membership in `Z` is local for the fppf topology, because `Z` is a subsheaf, so it may be
  checked after the surjective étale base change of a scheme chart of `X`
  (`AlgebraicGeometry.Space.mem_obj_of_surjective_etale`).

## Main results

* `AlgebraicGeometry.Scheme.ker_le_ker_iff_of_isAffine`: over an affine base, an inclusion of
  the ideal sheaf of a closed immersion into the kernel of another morphism is the inclusion
  of the kernels on global sections.
* `AlgebraicGeometry.Space.exists_comp_eq_of_ker_le`: a morphism of the big fppf category over
  `S` whose kernel contains that of a closed immersion of the category factors through it.
* `AlgebraicGeometry.Space.mem_obj_iff_ker_le` and
  `AlgebraicGeometry.Space.mem_obj_iff_definingIdealAt_le`: the chart-local membership
  criterion, in the ideal sheaf form and — on an affine chart — in the form of
  `AlgebraicGeometry.Space.definingIdealAt`.
* `AlgebraicGeometry.Space.mem_obj_of_sieve_le` and
  `AlgebraicGeometry.Space.mem_obj_of_surjective_etale`: membership in a subsheaf of a sheaf on
  the big fppf category over `S` is local, respectively for a covering sieve and for a single
  surjective étale morphism.
* `AlgebraicGeometry.Space.yonedaEquiv_yoneda_map_comp`: the Yoneda section attached to a
  composite with a represented morphism is the value of the morphism of presheaves at that
  morphism of the site.  This is how a point of `X` which factors through a chart is recognised,
  so it is also what any further consumer of the chart-local criterion needs.
* `AlgebraicGeometry.Space.exists_comp_eq_iff_forall_ker_le` is the factorization criterion of
  Stacks 03MB, read chart by chart.
* `AlgebraicGeometry.Space.definingIdealAt_le_ker_of_comp_eq` is the vanishing half of that
  criterion read on an arbitrary chart, affine or not, through
  `AlgebraicGeometry.Space.definingIdealAt`.

The surjectivity clause of Stacks 03MB — that the structure map `𝒪_X ⟶ i_*𝒪_Z` of a closed
immersion is surjective — is a statement about the small étale site rather than about the
factorization criterion, and is
`AlgebraicGeometry.Space.isLocallySurjective_structureSharp` in
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionStructureMap.lean`.

## Implementation notes

`AlgebraicGeometry.Scheme.ker_le_ker_iff_of_isAffine` is one direction of Mathlib's
`AlgebraicGeometry.Scheme.ker_of_isAffine` composed with monotonicity of
`AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop`; the other direction needs
`AlgebraicGeometry.Scheme.Hom.ker_apply`, hence quasi-compactness of the closed immersion,
which is automatic.  Affineness of the *base* is genuinely needed there and nothing is assumed
of the source: it is what makes the ideal sheaf of the closed immersion recoverable from its
ideal of global sections.

Affineness is not assumed in `AlgebraicGeometry.Space.exists_comp_eq_iff_forall_ker_le`,
because its reverse direction is applied at the chart that
`AlgebraicGeometry.IsAlgebraicSpace.exists_atlas` supplies, which is an arbitrary scheme.
This is why the ideal sheaf rather than its global sections is the right-hand side: on a
non-affine chart the ideal of global sections does not determine the ideal sheaf, so the
condition stated with `AlgebraicGeometry.Space.definingIdealAt` alone would be weaker at a
non-affine chart.  Stating the criterion with `definingIdealAt` quantified over the *affine*
charts would require covering that atlas chart by affine charts, which is not done here.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 01HP](https://stacks.math.columbia.edu/tag/01HP)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u

/-! ### Ideal sheaves over an affine base -/

/-- The ideal sheaf generated by the kernel of a morphism of schemes on global sections is
contained in the kernel of that morphism. -/
private theorem ofIdealTop_ker_appTop_le_ker {V W : Scheme.{u}} (q : V ⟶ W) :
    Scheme.IdealSheafData.ofIdealTop (RingHom.ker q.appTop.hom) ≤ q.ker := by
  rw [Scheme.Hom.ker, Scheme.IdealSheafData.le_ofIdeals_iff]
  intro A
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_leOfHom,
    Ideal.map_le_iff_le_comap, RingHom.comap_ker, ← CommRingCat.hom_comp, q.naturality]
  intro x hx
  rw [RingHom.mem_ker] at hx ⊢
  rw [CommRingCat.hom_comp, RingHom.comp_apply,
    show (CommRingCat.Hom.hom (Scheme.Hom.app q ⊤)) x = 0 from hx, map_zero]

/-- **Over an affine base, the ideal sheaf of a closed immersion is its ideal of global
sections.** For a closed immersion `p : A ⟶ W` into an affine scheme and any `q : V ⟶ W`, the
ideal sheaf of `p` is contained in the kernel of `q` exactly when the kernel of `p` on global
sections is contained in that of `q`. -/
theorem Scheme.ker_le_ker_iff_of_isAffine {A V W : Scheme.{u}} (p : A ⟶ W) (q : V ⟶ W)
    [IsClosedImmersion p] [IsAffine W] :
    p.ker ≤ q.ker ↔ RingHom.ker p.appTop.hom ≤ RingHom.ker q.appTop.hom := by
  refine ⟨fun h ↦ ?_, fun h ↦ (Scheme.ker_of_isAffine p).trans_le
    ((Scheme.IdealSheafData.le_of_isAffine (by simpa using h)).trans
      (ofIdealTop_ker_appTop_le_ker q))⟩
  refine le_trans (le_of_eq ?_) ((h ⟨⊤, isAffineOpen_top W⟩).trans (q.ideal_ker_le _))
  rw [Scheme.Hom.ker_apply]
  rfl

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Factoring through a closed immersion of the site -/

/-- **Factoring through a closed immersion of the big fppf category over `S`.** A morphism
`k : a ⟶ c` of the category whose kernel on underlying schemes contains the ideal sheaf of a
closed immersion `p : b ⟶ c` of the category factors through `p`.

This is Mathlib's universal property of closed immersions of schemes, with the resulting
morphism of schemes put back in the category by
`AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq`. -/
theorem exists_comp_eq_of_ker_le {a b c : BigFppfOver B S hS} (p : b ⟶ c) (k : a ⟶ c)
    (hp : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map p))
    (hle : ((BigFppfOver.toScheme B S hS).map p).ker ≤
      ((BigFppfOver.toScheme B S hS).map k).ker) :
    ∃ ψ : a ⟶ b, ψ ≫ p = k := by
  have := hp
  set χ := _root_.AlgebraicGeometry.IsClosedImmersion.lift
    ((BigFppfOver.toScheme B S hS).map p) ((BigFppfOver.toScheme B S hS).map k) hle
  have hχ : χ ≫ (BigFppfOver.toScheme B S hS).map p = (BigFppfOver.toScheme B S hS).map k :=
    _root_.AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
  obtain ⟨ψ, hψ⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS χ (by
    rw [← BigFppfOver.toScheme_map_comp_hom p, ← Category.assoc, hχ,
      BigFppfOver.toScheme_map_comp_hom])
  exact ⟨ψ, (BigFppfOver.toScheme B S hS).map_injective (by rw [Functor.map_comp, hψ, hχ])⟩

/-! ### The chart-local membership criterion -/

/-- **A point of `X` lying over an étale chart lies in a closed subspace exactly when the
defining ideal of that chart dies on it.** For an étale scheme chart `U` of `X` and a morphism
`k : a ⟶ U` of the site, the point `k ≫ (U ⟶ X)` of `X` over `a` lies in the closed subspace
`Z` precisely when the ideal sheaf of the closed immersion of schemes `Z ×_X U ⟶ U` is
contained in the kernel of `k`.

This is the formula `Z(T) = {h : T ⟶ X ∣ h^*𝓘 ⟶ 𝒪_T` is zero`}` of Stacks 03MB, read on a
chart. -/
theorem mem_obj_iff_ker_le (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (U : SmallEtale B S hS X.1)
    {a : BigFppfOver B S hS} (k : a ⟶ U.1.left) :
    U.1.hom.app (op a) k ∈ Z.1.obj (op a) ↔
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd U.1.hom)).ker ≤
        ((BigFppfOver.toScheme B S hS).map k).ker := by
  rw [mem_obj_iff_exists_comp B S hS Z.1 (Z.2.2.rep.isPullback U.1.hom) (op a) k]
  refine ⟨?_, exists_comp_eq_of_ker_le B S hS _ _
    (Z.2.2.property U.1.hom _ _ (Z.2.2.rep.isPullback U.1.hom))⟩
  rintro ⟨ψ, rfl⟩
  rw [Functor.map_comp]
  exact Scheme.Hom.le_ker_comp _ _

/-- **The chart-local membership criterion through the defining ideal.** On an *affine* étale
scheme chart `U` of `X`, the point `k ≫ (U ⟶ X)` of `X` over `a` lies in the closed subspace
`Z` precisely when `AlgebraicGeometry.Space.definingIdealAt` of `Z` at `U` is killed by
pullback of regular functions along `k`. -/
theorem mem_obj_iff_definingIdealAt_le (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (U : SmallEtale B S hS X.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left)]
    {a : BigFppfOver B S hS} (k : a ⟶ U.1.left) :
    U.1.hom.app (op a) k ∈ Z.1.obj (op a) ↔
      definingIdealAt B S hS X Z (op U) ≤
        RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom := by
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd U.1.hom)) :=
    Z.2.2.property U.1.hom _ _ (Z.2.2.rep.isPullback U.1.hom)
  rw [mem_obj_iff_ker_le, Scheme.ker_le_ker_iff_of_isAffine, definingIdealAt_eq_ker,
    Scheme.Γ_map_op, Scheme.Γ_map_op]
  rfl

/-! ### Membership in a subsheaf is local -/

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Membership in a subsheaf is local.** A section of a sheaf on the big fppf category over
`S` which lies in a subsheaf of it after restriction along every arrow of a covering sieve
lies in that subsheaf. -/
theorem mem_obj_of_sieve_le (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (W : Subfunctor F) (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W.toFunctor)
    {T : BigFppfOver B S hS} (x : F.obj (op T)) (R : Sieve T)
    (hR : R ∈ BigFppfOver.topology B S hS T)
    (hmem : ∀ {V : BigFppfOver B S hS} (m : V ⟶ T), R m → F.map m.op x ∈ W.obj (op V)) :
    x ∈ W.obj (op T) :=
  (Subfunctor.isSheaf_iff W ((isSheaf_iff_isSheaf_of_type _ _).1 hF)).1
    ((isSheaf_iff_isSheaf_of_type _ _).1 hW) (op T) x
    ((BigFppfOver.topology B S hS).superset_covering (fun _ m hm ↦ hmem m hm) hR)

/-- **Membership in a subsheaf may be checked after a surjective étale base change.** A single
surjective étale morphism of the big fppf category over `S` generates a covering sieve, so a
section lying in a subsheaf after restriction along it already lies in that subsheaf. -/
theorem mem_obj_of_surjective_etale (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (W : Subfunctor F) (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W.toFunctor)
    {T' T : BigFppfOver B S hS} (q : T' ⟶ T)
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    (x : F.obj (op T)) (hx : F.map q.op x ∈ W.obj (op T')) :
    x ∈ W.obj (op T) := by
  refine mem_obj_of_sieve_le B S hS hF W hW x _
    (sieve_generate_singleton_mem_topology_over B S hS q hqs hqe) ?_
  rintro V m ⟨Y, a, b, hb, hfac⟩
  cases hb
  rw [← hfac, op_comp, Functor.map_comp_apply]
  exact W.map a.op hx

/-- The Yoneda section attached to a composite with a represented morphism is the value of the
morphism of presheaves at that morphism of the site. -/
theorem yonedaEquiv_yoneda_map_comp {a c : BigFppfOver B S hS}
    (g : yoneda.obj c ⟶ F) (m : a ⟶ c) :
    yonedaEquiv (yoneda.map m ≫ g) = g.app (op a) m := by
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-! ### Stacks 03MB: the factorization criterion -/

/-- **The converse half of Stacks 03MB on points.** If the defining ideal of a closed subspace
`Z ⊆ X` vanishes on every chart after pullback along `h : Y ⟶ X`, then every point of `Y` maps
into `Z`. -/
private theorem range_le_of_forall_ker_le
    (X Y : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1) (h : Y ⟶ X)
    (hker : ∀ (U : SmallEtale B S hS X.1) (a : BigFppfOver B S hS) (k : a ⟶ U.1.left)
      (y : yoneda.obj a ⟶ Y.1), yoneda.map k ≫ U.1.hom = y ≫ h.hom →
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd U.1.hom)).ker ≤
          ((BigFppfOver.toScheme B S hS).map k).ker) :
    Subfunctor.range h.hom ≤ Z.1 := by
  rintro T _ ⟨x₀, rfl⟩
  obtain ⟨UX, f, hfS, hfE⟩ := X.2.exists_atlas
  set U : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk f, hfE⟩
  set τ : yoneda.obj T.unop ⟶ X.1 := yonedaEquiv.symm (h.hom.app T x₀) with hτ
  have hτ' : τ = yonedaEquiv.symm x₀ ≫ h.hom := by
    rw [hτ]
    exact yonedaEquiv.injective (by rw [yonedaEquiv_comp, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply])
  refine mem_obj_of_surjective_etale B S hS X.2.isSheaf Z.1 Z.2.1.isSheaf
    (hfE.rep.snd τ) (hfS.property_snd τ) (hfE.property_snd τ) _ ?_
  have hw : yoneda.map (hfE.rep.fst' τ) ≫ f = yoneda.map (hfE.rep.snd τ) ≫ τ := by
    rw [hfE.rep.map_fst' τ]
    exact hfE.rep.w τ
  have hval : X.1.map (hfE.rep.snd τ).op (h.hom.app T x₀) =
      U.1.hom.app (op (hfE.rep.pullback τ)) (hfE.rep.fst' τ) := by
    rw [show U.1.hom = f from rfl,
      ← yonedaEquiv_yoneda_map_comp B S hS f (hfE.rep.fst' τ), hw,
      ← yonedaEquiv_naturality, hτ, Equiv.apply_symm_apply]
  rw [hval, mem_obj_iff_ker_le]
  exact hker U _ (hfE.rep.fst' τ) (yoneda.map (hfE.rep.snd τ) ≫ yonedaEquiv.symm x₀)
    (by rw [show U.1.hom = f from rfl, hw, hτ', Category.assoc])

/-- If `h : Y ⟶ X` factors through the closed subspace `Z`, a point of `Y` whose image in `X`
factors through a chart `U` by `k` has `k` factoring through the cartesian projection
`Z ×_X U ⟶ U`. -/
private theorem exists_comp_snd_eq_of_comp_eq
    (X Y : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1) (h : Y ⟶ X)
    (g : Y ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (hg : g ≫ ObjectProperty.homMk Z.1.ι = h)
    (U : SmallEtale B S hS X.1) {a : BigFppfOver B S hS} (k : a ⟶ U.1.left)
    (y : yoneda.obj a ⟶ Y.1) (hy : yoneda.map k ≫ U.1.hom = y ≫ h.hom) :
    ∃ ψ : a ⟶ Z.2.2.rep.pullback U.1.hom, ψ ≫ Z.2.2.rep.snd U.1.hom = k :=
  ⟨_, Z.2.2.rep.lift_snd (g := U.1.hom) (y ≫ g.hom) k (by
    rw [Category.assoc, show g.hom ≫ Z.1.ι = h.hom from congrArg InducedCategory.Hom.hom hg, hy])⟩

/-- **The factorization criterion of Stacks 03MB, chart by chart.** A morphism `h : Y ⟶ X` of
algebraic spaces over `S` factors through a closed subspace `Z ⊆ X` exactly when the defining ideal
of `Z` vanishes after pullback along `h`: for every étale scheme chart `U` of `X` and every point
of `Y` over an object `a` of the site whose image in `X` factors through `U` by `k : a ⟶ U`,
the ideal sheaf of the closed immersion of schemes `Z ×_X U ⟶ U` is contained in the kernel of `k`.

Both directions are proved as in Stacks 03MB.  A factorization makes every point of `Y` a
point of `Z`, which by `AlgebraicGeometry.Space.mem_obj_iff_ker_le` is the stated inclusion of
ideal sheaves.  Conversely a closed subspace is a subfunctor, so a factorization exists as
soon as every point of `Y` lies in `Z`; that is checked after the surjective étale base change
of a scheme chart of `X`, where the inclusion of ideal sheaves produces the required
factorization of the chart through `Z ×_X U`. -/
@[ega "I 4.4.6"]
theorem exists_comp_eq_iff_forall_ker_le
    (X Y : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1) (h : Y ⟶ X) :
    (∃ g : Y ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS),
        g ≫ ObjectProperty.homMk Z.1.ι = h) ↔
      ∀ (U : SmallEtale B S hS X.1) (a : BigFppfOver B S hS) (k : a ⟶ U.1.left)
        (y : yoneda.obj a ⟶ Y.1), yoneda.map k ≫ U.1.hom = y ≫ h.hom →
          ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd U.1.hom)).ker ≤
            ((BigFppfOver.toScheme B S hS).map k).ker := by
  constructor
  · rintro ⟨g, hg⟩ U a k y hy
    obtain ⟨ψ, rfl⟩ := exists_comp_snd_eq_of_comp_eq B S hS X Y Z h g hg U k y hy
    rw [Functor.map_comp]
    exact Scheme.Hom.le_ker_comp _ _
  · intro hker
    have hrange := range_le_of_forall_ker_le B S hS X Y Z h hker
    exact ⟨ObjectProperty.homMk (Subfunctor.lift h.hom hrange),
      ObjectProperty.hom_ext _ (Subfunctor.lift_ι h.hom hrange)⟩

/-- **Stacks 03MB, the vanishing half through the defining ideal.** If `h : Y ⟶ X` factors
through the closed subspace `Z`, then on every étale scheme chart `U` of `X` — affine or not —
the defining ideal of `Z` at `U` is killed by pullback of regular functions to any point of
`Y` whose image in `X` factors through `U`. -/
theorem definingIdealAt_le_ker_of_comp_eq
    (X Y : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1) (h : Y ⟶ X)
    (g : Y ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (hg : g ≫ ObjectProperty.homMk Z.1.ι = h)
    (U : SmallEtale B S hS X.1) {a : BigFppfOver B S hS} (k : a ⟶ U.1.left)
    (y : yoneda.obj a ⟶ Y.1) (hy : yoneda.map k ≫ U.1.hom = y ≫ h.hom) :
    definingIdealAt B S hS X Z (op U) ≤
      RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom := by
  obtain ⟨ψ, rfl⟩ := exists_comp_snd_eq_of_comp_eq B S hS X Y Z h g hg U k y hy
  rw [definingIdealAt_eq_ker]
  exact ker_le_ker_comp B S hS _ _

end Space

end AlgebraicGeometry

end
