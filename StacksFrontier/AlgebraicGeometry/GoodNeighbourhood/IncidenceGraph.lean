module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.IncidenceFibre
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ZeroSchemeOpenNeighbourhood
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Trivialize
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.ChartSection

/-!
# The incidence family contains the variety over the nonvanishing locus of `w₀`

On the open `V ⊆ X` where `w₀` does not vanish, the incidence family
`V(vⱼ - tⱼ w₀) ⊆ X ×_k 𝔸^c_k` of SGA 4, Exposé XI, Proposition 3.3 is the graph of
`x ↦ (vⱼ(x) / w₀(x))ⱼ`: the first projection is an isomorphism from its part over `V` onto `V`.
This is how the variety becomes an open subscheme of the family of curves.

## Main results

* `AlgebraicGeometry.GoodNeighbourhood.existsUnique_smul_eq_of_forall_notMem_support`: division
  by a nowhere vanishing section of an invertible module.
* `AlgebraicGeometry.GoodNeighbourhood.exists_pullbackGlobalSections_transport`.
* `AlgebraicGeometry.GoodNeighbourhood.exists_isOpenImmersion_incidence`.

## References

* SGA 4, Tome 3, Exposé XI, Proposition 3.3.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

attribute [local instance] Stacks.ChernCap42.isInvertible_sheafObj_modulePullback

/-- **Division by a nowhere vanishing section.** If the zero scheme of a section `ω` of an
invertible module is empty, every global section is a unique multiple of `ω`. -/
theorem existsUnique_smul_eq_of_forall_notMem_support {Y : Scheme.{u}} (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M] (ω : Γ(M, ⊤))
    (h : ∀ y : Y, y ∉ ((zeroScheme Y M ω).support : Set Y)) (σ : Γ(M, ⊤)) :
    ∃! a : Γ(Y, ⊤), a • ω = σ := by
  have : Stacks.Ample.IsInvertibleModule Y M := ‹_›
  have hW : (⊤ : Y.Opens) ≤ Stacks.NonvanishingOpen.nonvanishingOpen Y M ω := fun y _ =>
    Stacks.Algebraization.mem_nonvanishingOpen_of_notMem_support_zeroScheme M ω (h y)
  have hb := Stacks.NonvanishingSpelling.bijective_smul Y M ω hW
  have hid : M.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op ω = ω := by
    rw [show (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)) = 𝟙 _ from rfl, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  simp only [hid] at hb
  obtain ⟨a, ha⟩ := hb.2 σ
  exact ⟨a, ha, fun b hb' => hb.1 (hb'.trans ha.symm)⟩

/-- **Transport of pulled-back sections along `m ≫ pr = m'`**: an injective additive map
`Γ(m^* pr^* L) ⟶ Γ(m'^* L)`, linear over `Γ(Y, 𝒪)`, sending `m^* pr^* σ` to `m'^* σ`. -/
theorem exists_pullbackGlobalSections_transport {Y P X : Scheme.{u}} (m : Y ⟶ P) (pr : P ⟶ X)
    (m' : Y ⟶ X) (hm : m ≫ pr = m') (L : X.Modules) :
    ∃ Φ : Γ((Scheme.Modules.pullback m).obj ((Scheme.Modules.pullback pr).obj L), ⊤) →+
        Γ((Scheme.Modules.pullback m').obj L, ⊤),
      Function.Injective Φ ∧
      (∀ σ, Φ (pullbackGlobalSections m _ (pullbackGlobalSections pr L σ)) =
        pullbackGlobalSections m' L σ) ∧
      ∀ (r : Γ(Y, ⊤)) x, Φ (r • x) = r • Φ x := by
  subst hm
  let φ := (Scheme.Modules.pullbackComp m pr).hom.app L
  exact ⟨(φ.app ⊤).hom, (ConcreteCategory.bijective_of_isIso (φ.app ⊤)).injective,
    fun σ => SectionsEqualizer.pullbackGlobalSections_comp m pr L σ,
    fun r x => Scheme.Modules.Hom.app_smul φ r x⟩

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) {c : ℕ} (L : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **The graph of `x ↦ (vⱼ(x)/w₀(x))ⱼ` is an open of the incidence family.** Let `V ⊆ X` be an
open on which `w₀` does not vanish. Over `V` the incidence family `V(vⱼ - tⱼ w₀) ⊆ X ×_k 𝔸^c_k`
is the graph of the morphism `V ⟶ 𝔸^c_k` with coordinates `vⱼ / w₀`: the first projection
restricted to the preimage of `V` is an isomorphism, so `V` is an open subscheme of the family,
lying over `V` itself. -/
theorem exists_isOpenImmersion_incidence (v : Fin c → Γ(L, ⊤)) (w₀ : Γ(L, ⊤)) (V : X.Opens)
    (hV : ∀ x ∈ V, x ∉ ((zeroScheme X L w₀).support : Set X)) :
    ∃ j : V.toScheme ⟶ (partialIdeal _ (incidenceSection p L v w₀) c).subscheme,
      IsOpenImmersion j ∧
      j ≫ (partialIdeal _ (incidenceSection p L v w₀) c).subschemeι ≫ pullback.fst _ _ = V.ι ∧
      Set.range j.base = ((partialIdeal _ (incidenceSection p L v w₀) c).subschemeι ≫
        pullback.fst _ _).base ⁻¹' (V : Set X) := by
  set τ := 𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k) with hτ
  set pr₁ := pullback.fst p τ with hpr₁
  set pr₂ := pullback.snd p τ with hpr₂
  set G := incidenceSection p L v w₀ with hG
  set I := partialIdeal _ G c with hI
  have hnv : ∀ {Y : Scheme.{u}} (g : Y ⟶ X), Set.range g.base ⊆ (V : Set X) → ∀ y : Y,
      y ∉ ((zeroScheme Y _ (pullbackGlobalSections g L w₀)).support : Set Y) := by
    intro Y g hg y hy
    have hzp : zeroScheme Y _ (pullbackGlobalSections g L w₀) = (zeroScheme X L w₀).comap g :=
      Stacks.Divisors.zeroScheme_pullback _ _ _
    rw [hzp, Scheme.IdealSheafData.support_comap] at hy
    exact hV _ (hg ⟨y, rfl⟩) hy
  have hVr : Set.range V.ι.base ⊆ (V : Set X) := by rw [Scheme.Opens.range_ι]
  choose a ha using fun j : Fin c => (existsUnique_smul_eq_of_forall_notMem_support _ _
    (hnv V.ι hVr) (pullbackGlobalSections V.ι L (v j))).exists
  let f : V.toScheme ⟶ 𝔸(ULift.{u} (Fin c); Spec (.of k)) :=
    AffineSpace.homOfVector (V.ι ≫ p) (fun j => a j.down)
  let Γg : V.toScheme ⟶ pullback p τ := pullback.lift V.ι f (by simp [f, τ])
  have hΓ₁ : Γg ≫ pr₁ = V.ι := pullback.lift_fst _ _ _
  have hΓ₂ : Γg ≫ pr₂ = f := pullback.lift_snd _ _ _
  -- a pullback of `G j` vanishes iff `vⱼ = (j-th coordinate) • w₀` after pullback
  have key : ∀ {Y : Scheme.{u}} (g : Y ⟶ pullback p τ) (m' : Y ⟶ X), g ≫ pr₁ = m' →
      ∀ j : Fin c, pullbackGlobalSections g _ (G j) = 0 ↔ pullbackGlobalSections m' L (v j) =
        (g ≫ pr₂).appTop (AffineSpace.coord _ (ULift.up j)) • pullbackGlobalSections m' L w₀ := by
    intro Y g m' hg j
    obtain ⟨Φ, hΦi, hΦ, hΦs⟩ := exists_pullbackGlobalSections_transport g pr₁ m' hg L
    rw [← map_eq_zero_iff Φ hΦi, ← sub_eq_zero (b := _ • _)]
    rw [hG, incidenceSection, map_sub, SectionsEqualizer.pullbackGlobalSections_smul, map_sub, hΦs,
      hΦ, hΦ]
    rfl
  -- the graph lies on the incidence family
  have hker : I ≤ Γg.ker := by
    refine iSup₂_le fun j _ => ?_
    refine (Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker _ _ _).1
      ((key Γg V.ι hΓ₁ j).2 ?_)
    rw [hΓ₂, show f.appTop (AffineSpace.coord _ (ULift.up j)) = a j from
      AffineSpace.homOfVector_appTop_coord _ _ _]
    exact (ha j).symm
  let Γ' : V.toScheme ⟶ I.subscheme :=
    IsClosedImmersion.lift I.subschemeι Γg (by rw [I.ker_subschemeι]; exact hker)
  have hΓ' : Γ' ≫ I.subschemeι = Γg := IsClosedImmersion.lift_fac _ _ _
  let O := (I.subschemeι ≫ pr₁) ⁻¹ᵁ V
  have hΓV : ∀ y, (I.subschemeι ≫ pr₁) (Γ' y) ∈ V := fun y => by
    rw [← Scheme.Hom.comp_apply, reassoc_of% hΓ', hΓ₁]
    exact y.2
  have hrange : Set.range Γ'.base ⊆ Set.range O.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hΓV y
  let Γ'' : V.toScheme ⟶ O.toScheme := IsOpenImmersion.lift O.ι Γ' hrange
  have hΓ'' : Γ'' ≫ O.ι = Γ' := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ⟩ : ∃ φ : O.toScheme ⟶ V.toScheme, φ ≫ V.ι = O.ι ≫ I.subschemeι ≫ pr₁ :=
    ⟨_, morphismRestrict_ι _ _⟩
  have h1 : Γ'' ≫ φ = 𝟙 _ := by
    rw [← cancel_mono V.ι, Category.assoc, hφ, reassoc_of% hΓ'', reassoc_of% hΓ', hΓ₁,
      Category.id_comp]
  -- the incidence family over `V` is the graph
  have hcoord : ∀ i : ULift.{u} (Fin c),
      φ.appTop (a i.down) = (O.ι ≫ I.subschemeι ≫ pr₂).appTop (AffineSpace.coord _ i) := by
    intro i
    set m := O.ι ≫ I.subschemeι with hm
    have hm0 : pullbackGlobalSections m _ (G i.down) = 0 := by
      refine (Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker _ _ _).2
        (le_trans ?_ (Scheme.Hom.le_ker_comp O.ι I.subschemeι))
      rw [I.ker_subschemeι]
      exact le_iSup₂_of_le (f := fun (j : Fin c) (_ : j.val < c) => zeroScheme _ _ (G j))
        i.down i.down.2 le_rfl
    obtain ⟨Ψ, -, hΨ, hΨs⟩ := exists_pullbackGlobalSections_transport φ V.ι (φ ≫ V.ι) rfl L
    have e1 := (key m (φ ≫ V.ι) (by rw [hφ, hm, Category.assoc]) i.down).1 hm0
    have e2 : pullbackGlobalSections (φ ≫ V.ι) L (v i.down) =
        φ.appTop (a i.down) • pullbackGlobalSections (φ ≫ V.ι) L w₀ := by
      calc pullbackGlobalSections (φ ≫ V.ι) L (v i.down)
          = Ψ (pullbackGlobalSections φ _ (pullbackGlobalSections V.ι L (v i.down))) :=
            (hΨ _).symm
        _ = Ψ (pullbackGlobalSections φ _ (a i.down • pullbackGlobalSections V.ι L w₀)) := by
            rw [ha i.down]
        _ = Ψ (φ.appTop (a i.down) •
            pullbackGlobalSections φ _ (pullbackGlobalSections V.ι L w₀)) :=
            congrArg Ψ (SectionsEqualizer.pullbackGlobalSections_smul _ _ _ _)
        _ = φ.appTop (a i.down) •
            Ψ (pullbackGlobalSections φ _ (pullbackGlobalSections V.ι L w₀)) :=
            hΨs _ _
        _ = φ.appTop (a i.down) • pullbackGlobalSections (φ ≫ V.ι) L w₀ := by rw [hΨ]
    have hrφ : Set.range (φ ≫ V.ι).base ⊆ (V : Set X) := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hVr ⟨φ y, rfl⟩
    obtain ⟨a', -, ha'⟩ := existsUnique_smul_eq_of_forall_notMem_support
      ((Scheme.Modules.pullback (φ ≫ V.ι)).obj L) (pullbackGlobalSections (φ ≫ V.ι) L w₀)
      (hnv (φ ≫ V.ι) hrφ) (pullbackGlobalSections (φ ≫ V.ι) L (v i.down))
    exact (ha' _ e2.symm).trans (ha' _ e1.symm).symm
  have h2 : φ ≫ Γg = O.ι ≫ I.subschemeι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hΓ₁, hφ, Category.assoc]
    · rw [Category.assoc, hΓ₂]
      apply AffineSpace.hom_ext
      · rw [Category.assoc, AffineSpace.homOfVector_over, ← Category.assoc, hφ, Category.assoc,
          Category.assoc, Category.assoc, Category.assoc, pullback.condition]
      · intro i
        change φ.appTop (f.appTop _) = (O.ι ≫ I.subschemeι ≫ pr₂).appTop _
        rw [← hcoord i, AffineSpace.homOfVector_appTop_coord]
  have h3 : φ ≫ Γ'' = 𝟙 _ := by
    rw [← cancel_mono (O.ι ≫ I.subschemeι), Category.assoc, reassoc_of% hΓ'', hΓ', h2,
      Category.id_comp]
  have : IsIso Γ'' := ⟨⟨φ, h1, h3⟩⟩
  have hoi : IsOpenImmersion (Γ'' ≫ O.ι) := inferInstance
  rw [hΓ''] at hoi
  refine ⟨Γ', hoi, by rw [reassoc_of% hΓ', hΓ₁], ?_⟩
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact hΓV y
  · intro hz
    let w : O.toScheme := ⟨z, hz⟩
    have e : Γ'' (φ w) = w := by
      have := congrArg (fun g : O.toScheme ⟶ O.toScheme => g.base w) h3
      simpa using this
    refine ⟨φ w, ?_⟩
    rw [← hΓ'', Scheme.Hom.comp_apply, e]
    rfl

end AlgebraicGeometry.GoodNeighbourhood

end
