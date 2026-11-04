module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.InfinitesimalNeighbourhood.ChartReduction

/-!
# The `k`-th infinitesimal neighbourhood of the reduction is independent of the chart

Let `W` be a formal algebraic space with reduction `W_red` and let `f : Spf A ⟶ W` and
`f' : Spf A' ⟶ W` be affine formal charts, representable by algebraic spaces and étale. If a
section of `Spf A` over an object `T` lies in the stage `Spec(A/𝔞^(k+1))` and has the same image
in `W` as a section `y` of `Spf A'`, then `y` lies in the stage `Spec(A'/𝔞'^(k+1))`. This is the
step of Stacks 0GHM that makes the subsheaves `W_k ⊆ W` well defined: over an affine object both
sections cut out the same closed subscheme `T ×_W W_red`, whose ideal is the image of `𝔞` and of
`𝔞'`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_siteHom_ker_appTop_eq`: an ideal of the ring of an affine
  object of the site is the kernel of a closed immersion of the site.
* `AlgebraicGeometry.FormalSpace.mem_range_powStage_of_eq`: the statement above.

## References

* [Stacks Project, Tag 0GHM](https://stacks.math.columbia.edu/tag/0GHM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalRing

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An ideal `K` of the ring of an affine object `T` of the site is the kernel on global sections
of a closed immersion `T' ⟶ T` of the site, namely of the closed subscheme cut out by `K`. -/
theorem exists_siteHom_ker_appTop_eq (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (K : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    ∃ (T' : BigFppfOver B S hS) (h : T' ⟶ T),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map h) ∧
        RingHom.ker ((BigFppfOver.toScheme B S hS).map h).appTop.hom = K := by
  let X := (BigFppfOver.toScheme B S hS).obj T
  let I : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop K
  let ι := I.subschemeι
  let T' : BigFppfOver B S hS := Over.mk (ObjectProperty.homMk
    (X := ⟨I.subscheme, Scheme.size_lt_of_isClosedImmersion ι T.left.2⟩) (Y := B.obj hS)
    (ι ≫ T.hom.hom))
  refine ⟨T', Over.homMk (ObjectProperty.homMk ι) rfl,
    inferInstanceAs (_root_.AlgebraicGeometry.IsClosedImmersion ι), ?_⟩
  show RingHom.ker ι.appTop.hom = K
  have h1 : ι.ker = I := Scheme.IdealSheafData.ker_subschemeι I
  rw [Scheme.ker_of_isAffine ι] at h1
  exact (Scheme.IdealSheafData.equivOfIsAffine (X := X)).symm.injective h1

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]

/-- The weak ideal of definition `𝔞^(k+1)`, when it is open. -/
abbrev powNilWeakIdeal (hopen : ∀ k : ℕ, IsOpen ((topologicalNilradical A ^ (k + 1) : Ideal A) :
    Set A)) (k : ℕ) : { I : Ideal A // IsWeakIdealOfDefinition I } :=
  ⟨topologicalNilradical A ^ (k + 1), hopen k, fun _ hx =>
    IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp
      (Ideal.pow_le_self (Nat.succ_ne_zero k) hx)⟩

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- A section of a formal spectrum lying in a stage, read as a morphism of the site into that
stage. -/
theorem exists_siteHom_of_mem_range_stageIncl (D : QuotientSystem B S hS A)
    (L : { I : Ideal A // IsWeakIdealOfDefinition I }) {T : BigFppfOver B S hS}
    {x : (formalSpectrum D).obj.obj (op T)}
    (hx : x ∈ (Subfunctor.range (stageIncl D L).hom).obj (op T)) :
    ∃ g : T ⟶ D.stageObj L, (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm x =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g ≫ stageIncl D L := by
  let Jt := BigFppfOver.topology B S hS
  have : Jt.Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨z₀, rfl⟩ := hx
  refine ⟨(Sheaf.sheafifiedYoneda Jt).preimage ((Sheaf.sectionEquiv Jt).symm z₀), ?_⟩
  rw [Functor.map_preimage]
  apply (Sheaf.sectionEquiv Jt).injective
  rw [Sheaf.sectionEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- Conversely a morphism of the site into a stage gives a section in the range of the stage. -/
theorem mem_range_stageIncl_of_eq (D : QuotientSystem B S hS A)
    (L : { I : Ideal A // IsWeakIdealOfDefinition I }) {T : BigFppfOver B S hS}
    {x : (formalSpectrum D).obj.obj (op T)} (g : T ⟶ D.stageObj L)
    (hg : (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm x =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g ≫ stageIncl D L) :
    x ∈ (Subfunctor.range (stageIncl D L).hom).obj (op T) := by
  refine ⟨Sheaf.sectionEquiv _ ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g),
    ?_⟩
  rw [← Sheaf.sectionEquiv_comp, ← hg, Equiv.apply_symm_apply]

/-- A morphism `T' ⟶ Spec(A/J) ⟶ Spec A` factors through `Spec(A/L)` exactly when its ring map
kills `L`. -/
theorem exists_factor_stageQuotientSpecMap_iff (D : QuotientSystem B S hS A)
    (L : { I : Ideal A // IsWeakIdealOfDefinition I }) {X : Scheme.{u}}
    (φ : X ⟶ Spec (.of A)) :
    (∃ l : X ⟶ (BigFppfOver.toScheme B S hS).obj (D.stageObj L),
        l ≫ stageQuotientSpecMap D L = φ) ↔
      ∀ ξ : Γ(Spec (.of A), ⊤), (Scheme.ΓSpecIso (.of A)).hom ξ ∈ L.1 → φ.appTop ξ = 0 := by
  have : _root_.AlgebraicGeometry.IsClosedImmersion (stageQuotientSpecMap D L) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  rw [Scheme.exists_factor_iff_ker_appTop_le]
  exact ⟨fun h ξ hξ => h ((mem_ker_specMap_quotient_appTop_iff L.1 ξ).2 hξ),
    fun h ξ hξ => h ξ ((mem_ker_specMap_quotient_appTop_iff L.1 ξ).1 hξ)⟩

/-- **The `k`-th stage is independent of the chart, over an affine object.** -/
theorem mem_range_powStage_of_eq_of_isAffine
    {A' : Type u} [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A']
    [IsLinearTopology A' A'] (hA : IsWeaklyAdmissible A) (hA' : IsWeaklyAdmissible A')
    (hopen : ∀ k : ℕ, IsOpen ((topologicalNilradical A ^ (k + 1) : Ideal A) : Set A))
    (hopen' : ∀ k : ℕ, IsOpen ((topologicalNilradical A' ^ (k + 1) : Ideal A') : Set A'))
    (D : QuotientSystem B S hS A) (D' : QuotientSystem B S hS A')
    {W Wred : FppfSheaf B S hS} {i : Wred ⟶ W} (hred : IsReduction B S hS W Wred i)
    (f : formalSpectrum D ⟶ W) (f' : formalSpectrum D' ⟶ W)
    (hfrep' : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f'.hom)
    (hfet' : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f'.hom hfrep')
    (k : ℕ) {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    {x : (formalSpectrum D).obj.obj (op T)}
    (hx : x ∈ (Subfunctor.range (stageIncl D (powNilWeakIdeal hopen k)).hom).obj (op T))
    (y : (formalSpectrum D').obj.obj (op T)) (hxy : f.hom.app (op T) x = f'.hom.app (op T) y) :
    y ∈ (Subfunctor.range (stageIncl D' (powNilWeakIdeal hopen' k)).hom).obj (op T) := by
  classical
  let Jt := BigFppfOver.topology B S hS
  let q := BigFppfOver.toScheme B S hS
  let a := topologicalNilradical A
  let a' := topologicalNilradical A'
  obtain ⟨g, hg⟩ := exists_siteHom_of_mem_range_stageIncl D _ hx
  obtain ⟨J', g', hg'₀⟩ := exists_stage_hom hA' D' T ((Sheaf.sectionEquiv Jt).symm y)
  have hg' : (Sheaf.sectionEquiv Jt).symm y =
      (Sheaf.sheafifiedYoneda Jt).map g' ≫ stageIncl D' J' := hg'₀
  let ψ := (q.map g ≫ stageQuotientSpecMap D (powNilWeakIdeal hopen k)).appTop
  let ψ' := (q.map g' ≫ stageQuotientSpecMap D' J').appTop
  let c := Ideal.comap (Scheme.ΓSpecIso (.of A)).hom.hom a
  let K := Ideal.map ψ.hom c
  obtain ⟨T', h₀, -, hker⟩ := exists_siteHom_ker_appTop_eq T K
  -- the restriction of `x` to `T'` lies in the reduction stage
  have hx₀ : (formalSpectrum D).obj.map h₀.op x ∈
      (Subfunctor.range (stageIncl D (nilWeakIdeal hA)).hom).obj (op T') := by
    obtain ⟨z, hz⟩ := (stage_factor_iff hA D (powNilWeakIdeal hopen k) (nilWeakIdeal hA) g h₀).2
      ((exists_factor_stageQuotientSpecMap_iff D _ _).2 fun ξ hξ => by
        have hξK : ψ ξ ∈ K := Ideal.mem_map_of_mem _ (show ξ ∈ c from hξ)
        rw [← hker] at hξK
        rw [q.map_comp, Category.assoc, Scheme.Hom.comp_appTop]
        exact hξK)
    refine mem_range_stageIncl_of_eq D _ z ?_
    rw [hz]
    apply (Sheaf.sectionEquiv Jt).injective
    rw [Equiv.apply_symm_apply, Functor.map_comp, Category.assoc, Sheaf.sectionEquiv_map_comp,
      ← hg, Equiv.apply_symm_apply]
  -- hence it maps into `W_red`, and so does the restriction of `y`
  obtain ⟨r, hr⟩ := exists_mapsTo_reduction_of_mem_range_nilStage hA D hred f _ hx₀
  have hy₀ := mem_range_nilStage_of_mapsTo_reduction hA' D' hred f' hfrep' hfet'
    ((formalSpectrum D').obj.map h₀.op y) r (by
      rw [hr, NatTrans.naturality_apply, hxy, ← NatTrans.naturality_apply])
  -- so `ψ'` carries `𝔞'` into `K`
  obtain ⟨z', hz'⟩ := exists_siteHom_of_mem_range_stageIncl D' _ hy₀
  obtain ⟨l', hl'⟩ := (stage_factor_iff hA' D' J' (nilWeakIdeal hA') g' h₀).1 ⟨z', by
    rw [← hz']
    apply (Sheaf.sectionEquiv Jt).injective
    rw [Equiv.apply_symm_apply, Functor.map_comp, Category.assoc, Sheaf.sectionEquiv_map_comp,
      ← hg', Equiv.apply_symm_apply]⟩
  have hψ' : Ideal.map ψ'.hom (Ideal.comap (Scheme.ΓSpecIso (.of A')).hom.hom a') ≤ K := by
    rw [Ideal.map_le_iff_le_comap]
    intro ξ hξ
    have := ((exists_factor_stageQuotientSpecMap_iff D' _ _).1 ⟨l', hl'⟩) ξ hξ
    rw [q.map_comp, Category.assoc, Scheme.Hom.comp_appTop] at this
    show ψ' ξ ∈ K
    rw [← hker]
    exact this
  -- and `K ^ (k + 1) = 0` because `ψ` kills `𝔞 ^ (k + 1)`
  have hK : K ^ (k + 1) = ⊥ := by
    show (Ideal.map ψ.hom c) ^ (k + 1) = ⊥
    rw [← Ideal.map_pow, eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro ξ hξ
    have hξ' : ξ ∈ Ideal.comap (Scheme.ΓSpecIso (.of A)).hom.hom (a ^ (k + 1)) :=
      Ideal.le_comap_pow _ (k + 1) hξ
    have := ((exists_factor_stageQuotientSpecMap_iff D (powNilWeakIdeal hopen k)
      (stageQuotientSpecMap D (powNilWeakIdeal hopen k))).1 ⟨𝟙 _, Category.id_comp _⟩) ξ hξ'
    show ψ ξ ∈ (⊥ : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    simp only [ψ, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, this,
      map_zero, Submodule.zero_mem]
  -- conclude
  obtain ⟨z, hz⟩ := (stage_factor_iff hA' D' J' (powNilWeakIdeal hopen' k) g' (𝟙 T)).2
    ((exists_factor_stageQuotientSpecMap_iff D' _ _).2 fun ξ hξ => by
      have hpow : ξ ∈ (Ideal.comap (Scheme.ΓSpecIso (.of A')).hom.hom a') ^ (k + 1) := by
        let e := (Scheme.ΓSpecIso (.of A')).commRingCatIsoToRingEquiv
        have h1 : Ideal.comap (Scheme.ΓSpecIso (.of A')).hom.hom (a' ^ (k + 1)) =
            (Ideal.comap (Scheme.ΓSpecIso (.of A')).hom.hom a') ^ (k + 1) := by
          show Ideal.comap e _ = (Ideal.comap e _) ^ (k + 1)
          rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]
        rw [← h1]
        exact hξ
      have hle : Ideal.map ψ'.hom ((Ideal.comap (Scheme.ΓSpecIso (.of A')).hom.hom a') ^ (k + 1))
          ≤ K ^ (k + 1) := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono hψ' (k + 1)
      have : ψ' ξ ∈ K ^ (k + 1) := hle (Ideal.mem_map_of_mem _ hpow)
      rw [hK] at this
      rw [Category.id_comp]
      exact this)
  refine mem_range_stageIncl_of_eq D' _ z ?_
  rw [hz, Category.id_comp, ← hg']

/-- The image of a stage in a formal spectrum is a sheaf. -/
theorem isSheaf_range_stageIncl (hA : IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
    (L : { I : Ideal A // IsWeakIdealOfDefinition I }) :
    Presieve.IsSheaf (BigFppfOver.topology B S hS)
      (Subfunctor.range (stageIncl D L).hom).toFunctor := by
  let Jt := BigFppfOver.topology B S hS
  have : Mono (stageIncl D L) :=
    mono_formalSpectrumInclusion_of_isWeaklyAdmissible hA D (OrderDual.toDual L)
  have : Mono (stageIncl D L).hom := (sheafToPresheaf Jt (Type (u + 1))).map_mono _
  exact (isSheaf_iff_isSheaf_of_type Jt _).1 ((Presheaf.isSheaf_of_iso_iff (asIso
    (Subfunctor.toRange (stageIncl D L).hom))).1 ((Sheaf.sheafifiedYoneda Jt).obj _).property)

/-- **The `k`-th stage is independent of the chart.** -/
theorem mem_range_powStage_of_eq
    {A' : Type u} [CommRing A'] [TopologicalSpace A'] [IsTopologicalRing A']
    [IsLinearTopology A' A'] (hA : IsWeaklyAdmissible A) (hA' : IsWeaklyAdmissible A')
    (hopen : ∀ k : ℕ, IsOpen ((topologicalNilradical A ^ (k + 1) : Ideal A) : Set A))
    (hopen' : ∀ k : ℕ, IsOpen ((topologicalNilradical A' ^ (k + 1) : Ideal A') : Set A'))
    (D : QuotientSystem B S hS A) (D' : QuotientSystem B S hS A')
    {W Wred : FppfSheaf B S hS} {i : Wred ⟶ W} (hred : IsReduction B S hS W Wred i)
    (f : formalSpectrum D ⟶ W) (f' : formalSpectrum D' ⟶ W)
    (hfrep' : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f'.hom)
    (hfet' : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) f'.hom hfrep')
    (k : ℕ) {T : BigFppfOver B S hS} {x : (formalSpectrum D).obj.obj (op T)}
    (hx : x ∈ (Subfunctor.range (stageIncl D (powNilWeakIdeal hopen k)).hom).obj (op T))
    (y : (formalSpectrum D').obj.obj (op T)) (hxy : f.hom.app (op T) x = f'.hom.app (op T) y) :
    y ∈ (Subfunctor.range (stageIncl D' (powNilWeakIdeal hopen' k)).hom).obj (op T) := by
  let Jt := BigFppfOver.topology B S hS
  let Rg := Subfunctor.range (stageIncl D' (powNilWeakIdeal hopen' k)).hom
  obtain ⟨ι, U, kk, haff, -, hmem⟩ := exists_affineOpenCover_mem T
  refine (Rg.isSheaf_iff ((isSheaf_iff_isSheaf_of_type _ _).1 (formalSpectrum D').property)).1
    (isSheaf_range_stageIncl hA' D' _) (op T) y (Jt.superset_covering ?_ hmem)
  rintro T' _ ⟨T'', g, _, ⟨j⟩, rfl⟩
  have := haff j
  have hj := mem_range_powStage_of_eq_of_isAffine hA hA' hopen hopen' D D' hred f f' hfrep' hfet' k
    ((Subfunctor.range (stageIncl D (powNilWeakIdeal hopen k)).hom).map (kk j).op hx)
    ((formalSpectrum D').obj.map (kk j).op y)
    (by rw [NatTrans.naturality_apply, hxy, ← NatTrans.naturality_apply])
  show (formalSpectrum D').obj.map (g ≫ kk j).op y ∈ Rg.obj (op T')
  rw [op_comp, FunctorToTypes.map_comp_apply]
  exact Rg.map g.op hj

end AlgebraicGeometry.FormalSpace

end
