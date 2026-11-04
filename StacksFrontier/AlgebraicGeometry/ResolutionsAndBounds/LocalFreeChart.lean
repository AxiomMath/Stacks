module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.LocalSyzygy

/-!
# A sheaf of modules with a local presentation and a free stalk is free near the point

Let `(X, 𝒪_X)` be a ringed space, `M` an `𝒪_X`-module and `x ∈ X`. Suppose that `M` has a
finite presentation on some neighbourhood of `x` and that the stalk `M_x` is free on a finite
basis. Then `M` is free on a neighbourhood of `x`. This is [Stacks, Tag 0B8J] with finite
presentation required only near the point; the argument is the one of
`Stacks.SheafOfModules.nonempty_over_iso_free_of_stalk_basis`, which only ever uses the
presentation near `x`.

The local presentation is supplied, for a module coherent near `x` on a ringed space with
coherent structure sheaf, by the syzygy step `Stacks.SheafHomInjective.exists_syzygy`.

## Main results

* `Stacks.SheafOfModules.exists_chart_of_localPresentation`: the chart data near `x` built from
  a local presentation and a basis of the stalk.
* `Stacks.SheafOfModules.nonempty_over_iso_free_of_localPresentation`: freeness near `x`.
* `Stacks.SheafHomInjective.nonempty_localPresentation_of_isCoherentOn`: a module coherent near
  `x` has a local presentation at `x`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace SheafOfModules

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology (X : Type u)) RingCat.{u}}

/-- The germ of a linear combination is the linear combination of the germs. -/
private theorem germ_sum_smul {M : SheafOfModules.{u} R} (x : X) {U : Opens X} (hx : x ∈ U)
    {ι : Type*} (t : Finset ι) (c : ι → ToType (R.obj.obj (op U)))
    (m : ι → ToType (M.val.obj (op U))) :
    germ M x hx (∑ i ∈ t, c i • m i)
      = ∑ i ∈ t, TopCat.Presheaf.germ R.obj U x hx (c i) • germ M x hx (m i) := by
  rw [germ_sum]
  exact Finset.sum_congr rfl fun i _ => germ_smul x hx (c i) (m i)

/-- Restricting a linear combination equation gives the equation with restricted terms. -/
private theorem res_eq_sum_smul (M : SheafOfModules.{u} R) {U V : Opens X} (f : V ⟶ U)
    {ι : Type*} {t : Finset ι} {c : ι → ToType (R.obj.obj (op U))}
    {n : ι → ToType (M.val.obj (op U))} {m : ToType (M.val.obj (op U))}
    (h : m = ∑ i ∈ t, c i • n i) :
    res M f m = ∑ i ∈ t, resR R f (c i) • res M f (n i) := by
  rw [h, res_sum_smul]

/-- **Chart data from a local presentation.** Near a point at which the stalk is free, sections
realising a basis of the stalk, together with matrices expressing them through the generators of
a local presentation and conversely, and the identities `A * B = 1` and `rel * B = 0`, all on one
neighbourhood. -/
lemma exists_chart_of_localPresentation (M : SheafOfModules.{u} R) (x : X)
    (LP : LocalPresentation M x)
    {ρ : Type u} [Fintype ρ] [DecidableEq ρ]
    (bas : Module.Basis ρ (ToType (TopCat.Presheaf.stalk R.obj x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x))) :
    ∃ (U : Opens X) (fU : U ⟶ LP.nhd) (_ : x ∈ U)
      (s : ρ → ToType (M.val.obj (op U)))
      (A : ρ → LP.Gen → ToType (R.obj.obj (op U)))
      (B : LP.Gen → ρ → ToType (R.obj.obj (op U))),
      (∀ i, s i = ∑ k : LP.Gen, A i k • res M fU (LP.gens k)) ∧
      (∀ k, res M fU (LP.gens k) = ∑ i : ρ, B k i • s i) ∧
      (∀ i i', ∑ k : LP.Gen, A i k * B k i' = if i = i' then 1 else 0) ∧
      (∀ l i, ∑ k : LP.Gen, resR R fU (LP.rel l k) * B k i = 0) := by
  classical
  obtain ⟨U₁, g₁, hxU₁, s₁, hs₁⟩ := exists_sections_germ_eq M x bas LP.nhd LP.mem_nhd
  choose Wa ga hxWa A₀ hA₀ using fun i : ρ => LP.generates g₁ (s₁ i) x hxU₁
  obtain ⟨U₂, g₂₁, hxU₂, hle₂⟩ := exists_nbhd_le' x U₁ hxU₁ Wa hxWa
  have hs₂ : ∀ i, germ M x hxU₂ (res M g₂₁ (s₁ i)) = bas i := fun i =>
    (germ_res x g₂₁ hxU₂ (s₁ i)).trans (hs₁ i)
  have hA₂ : ∀ i, res M g₂₁ (s₁ i) = ∑ k : LP.Gen,
      resR R (homOfLE (hle₂ i)) (A₀ i k) • res M (g₂₁ ≫ g₁) (LP.gens k) := fun i => by
    have h := res_eq_sum_smul M (homOfLE (hle₂ i) : U₂ ⟶ Wa i) (hA₀ i)
    simp only [res_res] at h
    exact h
  choose Wb gb hxWb B₀ hB₀ using fun k : LP.Gen =>
    exists_res_eq_sum_of_basis M x hxU₂ (fun i => res M g₂₁ (s₁ i)) bas hs₂
      (res M (g₂₁ ≫ g₁) (LP.gens k))
  obtain ⟨U₃, g₃₂, hxU₃, hle₃⟩ := exists_nbhd_le' x U₂ hxU₂ Wb hxWb
  -- the data over `U₃`
  set fU : U₃ ⟶ LP.nhd := g₃₂ ≫ (g₂₁ ≫ g₁)
  set s : ρ → ToType (M.val.obj (op U₃)) := fun i => res M (g₃₂ ≫ g₂₁) (s₁ i)
  set A : ρ → LP.Gen → ToType (R.obj.obj (op U₃)) :=
    fun i k => resR R (g₃₂ ≫ homOfLE (hle₂ i)) (A₀ i k)
  set B : LP.Gen → ρ → ToType (R.obj.obj (op U₃)) :=
    fun k i => resR R (homOfLE (hle₃ k)) (B₀ k i)
  have hgs : ∀ i, germ M x hxU₃ (s i) = bas i := fun i =>
    (germ_res x (g₃₂ ≫ g₂₁) hxU₃ (s₁ i)).trans (hs₁ i)
  have hA : ∀ i, s i = ∑ k : LP.Gen, A i k • res M fU (LP.gens k) := fun i => by
    simpa only [res_res, resR_resR] using res_eq_sum_smul M g₃₂ (hA₂ i)
  have hB : ∀ k, res M fU (LP.gens k) = ∑ i : ρ, B k i • s i := fun k => by
    have h := res_eq_sum_smul M (homOfLE (hle₃ k) : U₃ ⟶ Wb k) (hB₀ k)
    simp only [res_res] at h
    exact h
  -- the two identities, first at the level of germs
  have hgu : ∀ k, germ M x hxU₃ (res M fU (LP.gens k))
      = ∑ i : ρ, TopCat.Presheaf.germ R.obj U₃ x hxU₃ (B k i) • bas i := by
    intro k
    rw [hB k, germ_sum_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [hgs i]
  have hbasi : ∀ i, bas i = ∑ i' : ρ, (∑ k : LP.Gen,
      TopCat.Presheaf.germ R.obj U₃ x hxU₃ (A i k)
        * TopCat.Presheaf.germ R.obj U₃ x hxU₃ (B k i')) • bas i' := by
    intro i
    calc bas i = germ M x hxU₃ (s i) := (hgs i).symm
      _ = ∑ k : LP.Gen, TopCat.Presheaf.germ R.obj U₃ x hxU₃ (A i k)
            • germ M x hxU₃ (res M fU (LP.gens k)) := by
          rw [hA i, germ_sum_smul]
      _ = ∑ k : LP.Gen, TopCat.Presheaf.germ R.obj U₃ x hxU₃ (A i k)
            • (∑ i' : ρ, TopCat.Presheaf.germ R.obj U₃ x hxU₃ (B k i') • bas i') :=
          Finset.sum_congr rfl fun k _ => by rw [hgu k]
      _ = _ := sum_smul_sum_smul _ _ _
  -- coefficients of a vector with respect to `bas`
  have hcoef : ∀ (c : ρ → ToType (TopCat.Presheaf.stalk R.obj x)) (v : _),
      ∑ i' : ρ, c i' • bas i' = v → ∀ i', c i' = bas.repr v i' := fun c v h i' => by
    rw [← h, bas.repr_sum_self]
  have hid1g : ∀ i i', (∑ k : LP.Gen, TopCat.Presheaf.germ R.obj U₃ x hxU₃ (A i k)
      * TopCat.Presheaf.germ R.obj U₃ x hxU₃ (B k i')) = if i = i' then 1 else 0 := by
    intro i i'
    rw [hcoef _ _ (hbasi i).symm i', bas.repr_self]
    simp [Finsupp.single_apply]
  have hz : ∀ l, (∑ k : LP.Gen, resR R fU (LP.rel l k) • res M fU (LP.gens k))
      = (0 : ToType (M.val.obj (op U₃))) := by
    intro l
    rw [← res_sum_smul, LP.rel_apply, res_zero]
  have hid2g : ∀ (l : LP.Rel) (i : ρ), (∑ k : LP.Gen,
      TopCat.Presheaf.germ R.obj U₃ x hxU₃ (resR R fU (LP.rel l k))
        * TopCat.Presheaf.germ R.obj U₃ x hxU₃ (B k i)) = 0 := by
    intro l i
    have h0 : (∑ i' : ρ, (∑ k : LP.Gen,
        TopCat.Presheaf.germ R.obj U₃ x hxU₃ (resR R fU (LP.rel l k))
          * TopCat.Presheaf.germ R.obj U₃ x hxU₃ (B k i')) • bas i') = 0 := by
      rw [← sum_smul_sum_smul]
      calc (∑ k : LP.Gen, TopCat.Presheaf.germ R.obj U₃ x hxU₃ (resR R fU (LP.rel l k))
              • (∑ i' : ρ, TopCat.Presheaf.germ R.obj U₃ x hxU₃ (B k i') • bas i'))
          = ∑ k : LP.Gen, TopCat.Presheaf.germ R.obj U₃ x hxU₃ (resR R fU (LP.rel l k))
              • germ M x hxU₃ (res M fU (LP.gens k)) :=
            Finset.sum_congr rfl fun k _ => by rw [hgu k]
        _ = germ M x hxU₃ (∑ k : LP.Gen, resR R fU (LP.rel l k) • res M fU (LP.gens k)) :=
            (germ_sum_smul x hxU₃ _ _ _).symm
        _ = 0 := by rw [hz l, germ_zero]
    simpa using hcoef _ _ h0 i
  have hgerm : ∀ a b : LP.Gen → ToType (R.obj.obj (op U₃)),
      TopCat.Presheaf.germ R.obj U₃ x hxU₃ (∑ k, a k * b k)
        = ∑ k, TopCat.Presheaf.germ R.obj U₃ x hxU₃ (a k)
          * TopCat.Presheaf.germ R.obj U₃ x hxU₃ (b k) := fun a b => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => map_mul _ _ _
  -- shrink so that both identities hold as sections
  choose Wc gc hxWc hc using fun p : ρ × ρ => exists_resR_eq_zero x hxU₃
    ((∑ k : LP.Gen, A p.1 k * B k p.2) - (if p.1 = p.2 then 1 else 0)) (by
      rw [map_sub, hgerm, hid1g p.1 p.2]
      by_cases hp : p.1 = p.2 <;> simp [hp])
  choose Wd gd hxWd hd using fun p : LP.Rel × ρ => exists_resR_eq_zero x hxU₃
    (∑ k : LP.Gen, resR R fU (LP.rel p.1 k) * B k p.2) ((hgerm _ _).trans (hid2g p.1 p.2))
  obtain ⟨U₄, g₄₃, hxU₄, hle₄⟩ := exists_nbhd_le' x U₃ hxU₃
    (Sum.elim Wc Wd) (by rintro (p | p) <;> [exact hxWc p; exact hxWd p])
  -- a relation holding on a neighbourhood containing `U₄` holds on `U₄`
  have hz4 : ∀ {W : Opens X} {g : W ⟶ U₃} {a : ToType (R.obj.obj (op U₃))},
      resR R g a = 0 → U₄ ≤ W → resR R g₄₃ a = 0 := fun h hW => by
    have h2 := congrArg (resR R (homOfLE hW)) h
    rw [resR_resR, resR_zero] at h2
    exact h2
  refine ⟨U₄, g₄₃ ≫ fU, hxU₄, fun i => res M g₄₃ (s i),
    fun i k => resR R g₄₃ (A i k), fun k i => resR R g₄₃ (B k i), ?_, ?_, ?_, ?_⟩
  · intro i
    have h := res_eq_sum_smul M g₄₃ (hA i)
    simp only [res_res] at h
    exact h
  · intro k
    have h := res_eq_sum_smul M g₄₃ (hB k)
    simp only [res_res] at h
    exact h
  · intro i i'
    have h0 := hz4 (hc (i, i')) (hle₄ (Sum.inl (i, i')))
    rw [resR_sub, resR_sum, sub_eq_zero] at h0
    refine Eq.trans (Finset.sum_congr rfl fun k _ =>
      (resR_mul R g₄₃ (A i k) (B k i')).symm) (h0.trans ?_)
    by_cases hp : i = i' <;> simp [hp, resR_one, resR_zero]
  · intro l i
    have h0 := hz4 (hd (l, i)) (hle₄ (Sum.inr (l, i)))
    rw [resR_sum] at h0
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h0
    rw [resR_mul, resR_resR]

/-- **[Stacks, Tag 0B8J] near a point.** A sheaf of modules with a finite presentation near `x`
whose stalk at `x` is free on a finite basis is isomorphic to a free sheaf of modules on a
neighbourhood of `x`. -/
theorem nonempty_over_iso_free_of_localPresentation (M : SheafOfModules.{u} R) (x : X)
    (LP : LocalPresentation M x) {ρ : Type u} [Finite ρ]
    (bas : Module.Basis ρ (ToType (TopCat.Presheaf.stalk R.obj x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x))) :
    ∃ U : Opens X, x ∈ U ∧ Nonempty (M.over U ≅ free (R := R.over U) ρ) := by
  classical
  cases nonempty_fintype ρ
  obtain ⟨U, fU, hxU, s, A, B, hA, hB, hid1, hid2⟩ := exists_chart_of_localPresentation M x LP bas
  obtain ⟨hinj, hsurj⟩ :=
    inj_and_locally_surj_of_chart M x LP U fU s A B hA hB hid1 hid2
  exact ⟨U, hxU, nonempty_over_iso_free_of_inj_of_surj M s hinj hsurj⟩

end Stacks.SheafOfModules

namespace Stacks.SheafHomInjective

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology (X : Type u)) CommRingCat.{u}}

/-- The generating sections of a sheaf of modules given by an epimorphism from a free one. -/
def generatingSectionsOfEpi {W : Opens X} {ι : Type u}
    {M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf O).over W)}
    (g : SheafOfModules.free ι ⟶ M) [Epi g] : M.GeneratingSections where
  I := ι
  s := M.freeHomEquiv g
  epi := by
    rw [Equiv.symm_apply_apply]
    infer_instance

/-- The morphism from the free sheaf of modules defined by `generatingSectionsOfEpi g` is `g`. -/
theorem generatingSectionsOfEpi_π {W : Opens X} {ι : Type u}
    {M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf O).over W)}
    (g : SheafOfModules.free ι ⟶ M) [Epi g] : (generatingSectionsOfEpi g).π = g :=
  Equiv.symm_apply_apply _ _

/-- A morphism of modules whose cokernel vanishes on `U` is an epimorphism on `U`. -/
theorem epi_over_of_vanishesOn_cokernel
    {E E' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (f : E ⟶ E')
    {U : Opens X} (hf : VanishesOn (cokernel f) U) : Epi (f.over U) := by
  let Q := SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) U
  have hz : IsZero (cokernel (Q.map f)) :=
    (isZero_over_of_vanishesOn hf).of_iso (PreservesCokernel.iso Q f).symm
  exact Preadditive.epi_of_isZero_cokernel _ hz

/-- **A module coherent near `x` has a local presentation at `x`.** -/
theorem nonempty_localPresentation_of_isCoherentOn
    [Stacks.SheafOfModules.IsCoherent
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))]
    {A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} {W : Opens X}
    (hA : Stacks.SheafOfModules.IsCoherentOn A W) {y : X} (hy : y ∈ W) :
    Nonempty (Stacks.SheafOfModules.LocalPresentation A y) := by
  obtain ⟨U₀, hy₀, -, ι, hι, P, i, π, hi, hci, hcπ, hK⟩ := exists_syzygy hA hy
  obtain ⟨U₁, hy₁, hU₁, κ, hκ, ψ, hψ⟩ :=
    exists_epi_free_over_of_isFiniteType (hK U₀ le_rfl).1 hy₀
  have hiU : IsIso (i.over U₁) := by
    have : Epi (i.over U₁) := epi_over_of_vanishesOn_cokernel i (hci.mono hU₁)
    exact isIso_of_mono_of_epi _
  have hπU : Epi (π.over U₁) := epi_over_of_vanishesOn_cokernel π (hcπ.mono hU₁)
  let g : SheafOfModules.free ι ⟶ A.over U₁ :=
    (overFreeIso U₁ ι).inv ≫ inv (i.over U₁) ≫ π.over U₁
  have : Epi g := epi_comp _ _
  let σ := generatingSectionsOfEpi g
  let Q := SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) U₁
  let e : (kernel π).over U₁ ≅ kernel σ.π :=
    PreservesKernel.iso Q π ≪≫ (kernelIsIsoComp (inv (i.over U₁)) (π.over U₁)).symm ≪≫
      (kernelIsIsoComp (overFreeIso U₁ ι).inv (inv (i.over U₁) ≫ π.over U₁)).symm ≪≫
      kernelIsoOfEq (generatingSectionsOfEpi_π g).symm
  let τ := generatingSectionsOfEpi ψ
  let pres : (A.over U₁).Presentation :=
    { generators := σ
      relations := SheafOfModules.GeneratingSections.equivOfIso e τ }
  have : pres.IsFinite :=
    { isFiniteType_generators := ⟨hι⟩
      isFiniteType_relations := ⟨hκ⟩ }
  exact ⟨Stacks.SheafOfModules.localPresentationOfPresentation A pres hy₁⟩

end Stacks.SheafHomInjective

end
