module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerLocalEquation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerDirectImageCoboundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ZariskiRestrictionSheaf
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsBaseChange.Basic

/-!
# The fundamental class of a divisor in `R¹ j_* μ_N`, glued from local equations

Let `i : Z ⟶ U` be a closed immersion, `j : U₀ ⟶ U` an open immersion onto the complement of `Z`,
and `N` an integer invertible on `U`. A local equation `t` of `Z` on an open `V ⊆ U`
(`Stacks.EtaleCohomology.Purity.IsLocalEquation`) is invertible on `V ×_U U₀`, so it is a section
of `j_* 𝐆_m` over `V`; its Kummer coboundary `∂ t`
(`Stacks.EtaleCohomology.Purity.kummerDirectImageδ`) is a section of `R¹ j_* μ_N` over `V`
(`Stacks.EtaleCohomology.Purity.localKummerClass`).

It does not depend on the local equation
(`Stacks.EtaleCohomology.Purity.localKummerClass_eq_of_isLocalEquation`): near each point two
local equations differ by a unit of `U`, which `∂` kills
(`Stacks.EtaleCohomology.Purity.multiplicativeDirectImageComparison_comp_kummerDirectImageδ`), or
both vanish there, and then `V ×_U U₀` is empty near the point. Since an étale sheaf is a Zariski
sheaf, the classes `∂ t` glue to a unique global section of `R¹ j_* μ_N` as soon as every point of
`U` has a local equation around it
(`Stacks.EtaleCohomology.Purity.existsUnique_section_restrict_eq_localKummerClass`), e.g. for an
étale divisor of a smooth relative curve over a smooth `k`-scheme
(`Stacks.EtaleCohomology.Purity.exists_isLocalEquation`). This is the canonical section
`Stacks.EtaleCohomology.Purity.kummerDivisorSection`, the fundamental class of `Z`. The Kummer
class of a global function `f` with `Z = V(f)` set-theoretically would be the fundamental class
only up to the multiplicities of `f` along `Z`; local equations remove that ambiguity.

## Main definitions

* `Stacks.EtaleCohomology.Purity.puncturedFunction`: a function on `V` pulled back to `V ×_U U₀`.
* `Stacks.EtaleCohomology.Purity.localKummerClass`: the Kummer class `∂ t` of a local equation.
* `Stacks.EtaleCohomology.Purity.kummerDivisorSection`: the glued section of `R¹ j_* μ_N`.

## Main results

* `Stacks.EtaleCohomology.Purity.localKummerClass_restrict`.
* `Stacks.EtaleCohomology.Purity.localKummerClass_eq_of_isLocalEquation`.
* `Stacks.EtaleCohomology.Purity.existsUnique_section_restrict_eq_localKummerClass`.
* `Stacks.EtaleCohomology.Purity.kummerDivisorSection_restrict`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  TopologicalSpace Opposite

universe w u

namespace Stacks.EtaleCohomology.Purity

open Stacks.Kummer

section Punctured

variable {U₀ U : Scheme.{u}} (j : U₀ ⟶ U)

/-- `V ×_U U₀`, the étale `U₀`-scheme over which `j_* 𝐆_m` takes its sections over `V`. -/
abbrev puncturedOpen (V : U.Opens) : U₀.Etale :=
  (smallEtaleBaseChange j).obj ((opensToEtale U).obj V)

/-- The projection `V ×_U U₀ ⟶ U`. -/
abbrev puncturedOpenHom (V : U.Opens) : pullback V.ι j ⟶ U :=
  pullback.fst V.ι j ≫ V.ι

/-- The preimage of `V` under `V ×_U U₀ ⟶ U` is all of `V ×_U U₀`. -/
theorem top_le_preimage_puncturedOpenHom (V : U.Opens) :
    ⊤ ≤ puncturedOpenHom j V ⁻¹ᵁ V := by
  intro p _
  show V.ι ((pullback.fst V.ι j) p) ∈ V
  exact ((pullback.fst V.ι j) p).2

/-- **A function on `V`, pulled back to `V ×_U U₀`.** -/
def puncturedFunction (V : U.Opens) (t : Γ(U, V)) : Γ(pullback V.ι j, ⊤) :=
  (puncturedOpenHom j V).appLE V ⊤ (top_le_preimage_puncturedOpenHom j V) t

/-- `puncturedFunction` is multiplicative. -/
theorem puncturedFunction_mul (V : U.Opens) (a b : Γ(U, V)) :
    puncturedFunction j V (a * b) = puncturedFunction j V a * puncturedFunction j V b :=
  map_mul _ a b

/-- **A function invertible off `Z` is invertible on `V ×_U U₀`.** -/
theorem isUnit_puncturedFunction {Z : Scheme.{u}} {i : Z ⟶ U}
    (hj : Set.range j.base ⊆ (Set.range i.base)ᶜ) {V : U.Opens} {t : Γ(U, V)}
    (ht : (V : Set U) \ Set.range i.base ⊆ U.basicOpen t) :
    IsUnit (puncturedFunction j V t) := by
  have hle : ⊤ ≤ puncturedOpenHom j V ⁻¹ᵁ U.basicOpen t := by
    intro p _
    refine ht ⟨top_le_preimage_puncturedOpenHom j V trivial, ?_⟩
    have : (puncturedOpenHom j V) p = j ((pullback.snd V.ι j) p) := by
      rw [puncturedOpenHom, pullback.condition, Scheme.Hom.comp_apply]
    rw [this]
    exact hj ⟨_, rfl⟩
  have key : puncturedFunction j V t = (puncturedOpenHom j V).appLE (U.basicOpen t) ⊤ hle
      (U.presheaf.map (homOfLE (U.basicOpen_le t)).op t) := by
    rw [puncturedFunction, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rw [key]
  exact (U.toRingedSpace.isUnit_res_basicOpen t).map _

/-- The restriction `W ×_U U₀ ⟶ V ×_U U₀` for `W ⊆ V`: the base change along `j` of the
inclusion. -/
def puncturedRestriction {V W : U.Opens} (h : W ≤ V) : pullback W.ι j ⟶ pullback V.ι j :=
  pullback.map W.ι j V.ι j (U.homOfLE h) (𝟙 U₀) (𝟙 U) (by simp) (by simp)

/-- The restriction `W ×_U U₀ ⟶ V ×_U U₀` lies over the inclusion `W ⟶ V`. -/
theorem puncturedRestriction_fst {V W : U.Opens} (h : W ≤ V) :
    puncturedRestriction j h ≫ pullback.fst V.ι j = pullback.fst W.ι j ≫ U.homOfLE h :=
  pullback.lift_fst _ _ _

/-- Equal morphisms have equal `appLE`. -/
theorem appLE_eq_of_eq {X Y : Scheme.{u}} {f f' : X ⟶ Y} (hf : f = f') (U' : Y.Opens)
    (V' : X.Opens) (e : V' ≤ f ⁻¹ᵁ U') (e' : V' ≤ f' ⁻¹ᵁ U') :
    f.appLE U' V' e = f'.appLE U' V' e' := by
  subst hf; rfl

/-- The restriction `W ×_U U₀ ⟶ V ×_U U₀` commutes with the projections to `U`. -/
theorem puncturedRestriction_comp {V W : U.Opens} (h : W ≤ V) :
    puncturedRestriction j h ≫ puncturedOpenHom j V = puncturedOpenHom j W := by
  rw [puncturedOpenHom, ← Category.assoc, puncturedRestriction_fst, Category.assoc,
    U.homOfLE_ι]

/-- **Pulling back commutes with restriction.** -/
theorem appTop_puncturedFunction {V W : U.Opens} (h : W ≤ V) (t : Γ(U, V)) :
    (puncturedRestriction j h).appTop (puncturedFunction j V t) =
      puncturedFunction j W (U.presheaf.map (homOfLE h).op t) := by
  have key : (puncturedOpenHom j V).appLE V ⊤ (top_le_preimage_puncturedOpenHom j V) ≫
      (puncturedRestriction j h).appLE ⊤ ⊤ le_top =
      U.presheaf.map (homOfLE h).op ≫
        (puncturedOpenHom j W).appLE W ⊤ (top_le_preimage_puncturedOpenHom j W) := by
    refine (Scheme.Hom.appLE_comp_appLE (puncturedRestriction j h) (puncturedOpenHom j V)
      V ⊤ ⊤ _ _).trans ?_
    rw [Scheme.Hom.map_appLE]
    exact appLE_eq_of_eq (puncturedRestriction_comp j h) V ⊤ _ _
  rw [← Stacks.AlgebraicGeometry.GlobalSectionsBaseChange.appLE_top_top]
  exact congrArg (fun φ => φ.hom t) key

/-- `puncturedRestriction` is the base change along `j` of the inclusion of opens. -/
theorem smallEtaleBaseChange_map_opensToEtale_left {V W : U.Opens} (h : W ≤ V) :
    ((smallEtaleBaseChange j).map ((opensToEtale U).map (homOfLE h))).left =
      puncturedRestriction j h := by
  refine pullback.hom_ext ?_ ?_
  · exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
  · exact (pullback.lift_snd _ _ _).trans
      ((pullback.lift_snd _ _ _).trans (Category.comp_id _)).symm

/-- The function `t` on `V`, as a global function on the open subscheme `V`. -/
def openFunction (V : U.Opens) (t : Γ(U, V)) : Γ(V.toScheme, ⊤) :=
  V.ι.appLE V ⊤ (by simp) t

/-- `puncturedFunction` is the pullback along `V ×_U U₀ ⟶ V` of the function on `V`. -/
theorem puncturedFunction_eq_appTop (V : U.Opens) (t : Γ(U, V)) :
    puncturedFunction j V t = (pullback.fst V.ι j).appTop (openFunction V t) := by
  rw [← Stacks.AlgebraicGeometry.GlobalSectionsBaseChange.appLE_top_top _ le_top]
  exact congrArg (fun φ => φ.hom t)
    (Scheme.Hom.appLE_comp_appLE (pullback.fst V.ι j) V.ι V ⊤ ⊤ _ _).symm

end Punctured

section KummerClass

variable {U₀ U : Scheme.{u}} (j : U₀ ⟶ U)
  [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U₀) Ab.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U) Ab.{u + 1})] {N : ℕ}
  (hN0 : N ≠ 0) (hN : IsUnit ((N : ℕ) : Γ(U₀, ⊤)))

/-- `R¹ j_* μ_N`, the sheaf in which the fundamental class of the complement of `U₀` lives. -/
abbrev kummerTarget (j : U₀ ⟶ U) (N : ℕ) : Sheaf (smallEtaleTopology U) Ab.{u + 1} :=
  ((smallEtalePushforwardAb j).rightDerived 1).obj (rootsOfUnitySheaf.{u, 0} U₀ N)

/-- **The local Kummer class `∂ t`** of a function `t` on `V` invertible on `V ×_U U₀`: the Kummer
coboundary of `t`, viewed as a section of `j_* 𝐆_m` over `V`. -/
def localKummerClass (V : U.Opens) (t : Γ(U, V)) (ht : IsUnit (puncturedFunction j V t)) :
    ToType ((kummerTarget j N).obj.obj (op ((opensToEtale U).obj V))) :=
  (kummerDirectImageδ j hN0 hN).hom.app (op ((opensToEtale U).obj V))
    (ofUnit.{u, 0} (X := U₀) (U := puncturedOpen j V) ht.unit)

/-- **The local Kummer class restricts to the local Kummer class of the restriction.** -/
theorem localKummerClass_restrict {V W : U.Opens} (h : W ≤ V) (t : Γ(U, V))
    (ht : IsUnit (puncturedFunction j V t))
    (ht' : IsUnit (puncturedFunction j W (U.presheaf.map (homOfLE h).op t))) :
    (kummerTarget j N).obj.map ((opensToEtale U).map (homOfLE h)).op
        (localKummerClass j hN0 hN V t ht) =
      localKummerClass j hN0 hN W (U.presheaf.map (homOfLE h).op t) ht' := by
  have hnat := NatTrans.naturality_apply (kummerDirectImageδ j hN0 hN).hom
    ((opensToEtale U).map (homOfLE h)).op
    (ofUnit.{u, 0} (X := U₀) (U := puncturedOpen j V) ht.unit)
  refine hnat.symm.trans ((congrArg (ConcreteCategory.hom
    ((kummerDirectImageδ j hN0 hN).hom.app (op ((opensToEtale U).obj W))))
    (map_ofUnit.{u, 0} ((smallEtaleBaseChange j).map ((opensToEtale U).map (homOfLE h)))
      ht.unit)).trans ?_)
  refine congrArg (fun x => ConcreteCategory.hom
    ((kummerDirectImageδ j hN0 hN).hom.app (op ((opensToEtale U).obj W)))
      (ofUnit.{u, 0} (X := U₀) (U := puncturedOpen j W) x)) (Units.ext ?_)
  show ((smallEtaleBaseChange j).map ((opensToEtale U).map (homOfLE h))).left.appTop
    (puncturedFunction j V t) = puncturedFunction j W (U.presheaf.map (homOfLE h).op t)
  rw [smallEtaleBaseChange_map_opensToEtale_left]
  exact appTop_puncturedFunction j h t

omit [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U₀) Ab.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U) Ab.{u + 1})] in
/-- If `t` is invertible on `V ×_U U₀`, then its restriction to `W ⊆ V` is invertible on
`W ×_U U₀`. -/
theorem isUnit_puncturedFunction_restrict {V W : U.Opens} (h : W ≤ V) {t : Γ(U, V)}
    (ht : IsUnit (puncturedFunction j V t)) :
    IsUnit (puncturedFunction j W (U.presheaf.map (homOfLE h).op t)) := by
  rw [← appTop_puncturedFunction]
  exact ht.map _

/-- **The units of `U` have trivial local Kummer class.** -/
theorem localKummerClass_eq_zero_of_isUnit (hNU : IsUnit ((N : ℕ) : Γ(U, ⊤))) {V : U.Opens}
    {c : Γ(U, V)} (hc : IsUnit c) (hc' : IsUnit (puncturedFunction j V c)) :
    localKummerClass j hN0 hN V c hc' = 0 := by
  let x : (Γ(((opensToEtale U).obj V).left, ⊤))ˣ :=
    (hc.map (V.ι.appLE V ⊤ (by simp)).hom).unit
  have hx : ofUnit.{u, 0} (X := U₀) (U := puncturedOpen j V) hc'.unit =
      (multiplicativeDirectImageComparison.{u, 0} j).hom.app (op ((opensToEtale U).obj V))
        (ofUnit.{u, 0} x) := by
    rw [multiplicativeDirectImageComparison_app_ofUnit]
    refine congrArg _ (Units.ext ?_)
    exact puncturedFunction_eq_appTop j V c
  have h0 := congrArg (fun φ : multiplicativeSheaf.{u, 0} U ⟶ kummerTarget j N =>
      ConcreteCategory.hom (φ.hom.app (op ((opensToEtale U).obj V))) (ofUnit.{u, 0} x))
    (multiplicativeDirectImageComparison_comp_kummerDirectImageδ j hN0 hN hNU)
  rw [localKummerClass, hx]
  exact h0

/-- `localKummerClass_restrict`, with the unit hypothesis on the restriction filled in. -/
private theorem map_localKummerClass_restrict {V W : U.Opens} (h : W ≤ V) (t : Γ(U, V))
    (ht : IsUnit (puncturedFunction j V t)) :
    (kummerTarget j N).obj.map ((opensToEtale U).map (homOfLE h)).op
        (localKummerClass j hN0 hN V t ht) =
      localKummerClass j hN0 hN W (U.presheaf.map (homOfLE h).op t)
        (isUnit_puncturedFunction_restrict j h ht) :=
  localKummerClass_restrict j hN0 hN h t ht _

/-- **Local Kummer classes do not change under multiplication by a unit of `U`.** -/
theorem localKummerClass_eq_of_eq_unit_mul (hNU : IsUnit ((N : ℕ) : Γ(U, ⊤)))
    {V : U.Opens} {t₁ t₂ c : Γ(U, V)} (hc : IsUnit c) (h : t₁ = c * t₂)
    (ht₁ : IsUnit (puncturedFunction j V t₁)) (ht₂ : IsUnit (puncturedFunction j V t₂)) :
    localKummerClass j hN0 hN V t₁ ht₁ = localKummerClass j hN0 hN V t₂ ht₂ := by
  subst h
  have hc' : IsUnit (puncturedFunction j V c) :=
    isUnit_of_mul_isUnit_left (by rw [← puncturedFunction_mul]; exact ht₁)
  have hu : ht₁.unit = hc'.unit * ht₂.unit :=
    Units.ext (puncturedFunction_mul j V c t₂)
  have hsum : (ofUnit.{u, 0} (X := U₀) (U := puncturedOpen j V) ht₁.unit :
        ToType (((smallEtalePushforwardAb j).obj (multiplicativeSheaf.{u, 0} U₀)).obj.obj
          (op ((opensToEtale U).obj V)))) =
      ofUnit.{u, 0} (X := U₀) (U := puncturedOpen j V) hc'.unit +
        ofUnit.{u, 0} (X := U₀) (U := puncturedOpen j V) ht₂.unit := by
    rw [hu]; rfl
  have e : localKummerClass j hN0 hN V (c * t₂) ht₁ =
      localKummerClass j hN0 hN V c hc' + localKummerClass j hN0 hN V t₂ ht₂ :=
    (congrArg (ConcreteCategory.hom ((kummerDirectImageδ j hN0 hN).hom.app
      (op ((opensToEtale U).obj V)))) hsum).trans (map_add _ _ _)
  rw [e, localKummerClass_eq_zero_of_isUnit j hN0 hN hNU hc hc', zero_add]

/-- **Over a part of `V ×_U U₀` that is empty, all local Kummer classes agree.** -/
theorem localKummerClass_eq_of_eq_zero {V : U.Opens} {t₁ t₂ : Γ(U, V)}
    (ht₁ : IsUnit (puncturedFunction j V t₁)) (ht₂ : IsUnit (puncturedFunction j V t₂))
    (h0 : puncturedFunction j V t₁ = 0) :
    localKummerClass j hN0 hN V t₁ ht₁ = localKummerClass j hN0 hN V t₂ ht₂ := by
  have hz : IsUnit (0 : Γ(pullback V.ι j, ⊤)) := h0 ▸ ht₁
  have : Subsingleton Γ(pullback V.ι j, ⊤) := subsingleton_of_zero_eq_one (isUnit_zero_iff.1 hz)
  rw [localKummerClass, localKummerClass, Subsingleton.elim ht₁.unit ht₂.unit]

/-- The Zariski sheaf underlying `R¹ j_* μ_N`. -/
def kummerTargetZariski (j : U₀ ⟶ U) (N : ℕ) : TopCat.Sheaf Ab.{u + 1} U.toTopCat :=
  ⟨(opensToEtale U).op ⋙ (kummerTarget j N).obj, isSheaf_opensToEtale_op_comp U _⟩

/-- **The local Kummer class does not depend on the local equation.** -/
theorem localKummerClass_eq_of_isLocalEquation (hNU : IsUnit ((N : ℕ) : Γ(U, ⊤)))
    {Z : Scheme.{u}} {i : Z ⟶ U} [IsClosedImmersion i] {V : U.Opens} {t₁ t₂ : Γ(U, V)}
    (h₁ : IsLocalEquation i V t₁) (h₂ : IsLocalEquation i V t₂)
    (ht₁ : IsUnit (puncturedFunction j V t₁)) (ht₂ : IsUnit (puncturedFunction j V t₂)) :
    localKummerClass j hN0 hN V t₁ ht₁ = localKummerClass j hN0 hN V t₂ ht₂ := by
  choose O hOV hxO hO using fun x : V => h₁.exists_eq_unit_mul_or_eq_zero h₂ x.2
  refine TopCat.Sheaf.eq_of_locally_eq' (kummerTargetZariski j N) O V
    (fun x => homOfLE (hOV x)) (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxO ⟨y, hy⟩⟩) _ _ ?_
  intro x
  show (kummerTarget j N).obj.map ((opensToEtale U).map (homOfLE (hOV x))).op _ =
    (kummerTarget j N).obj.map ((opensToEtale U).map (homOfLE (hOV x))).op _
  rw [map_localKummerClass_restrict j hN0 hN (hOV x) t₁ ht₁,
    map_localKummerClass_restrict j hN0 hN (hOV x) t₂ ht₂]
  rcases hO x with ⟨c, hc, hct⟩ | h0
  · exact localKummerClass_eq_of_eq_unit_mul j hN0 hN hNU hc hct _ _
  · refine localKummerClass_eq_of_eq_zero j hN0 hN _ _ ?_
    rw [h0, puncturedFunction, map_zero]

/-- **The local Kummer classes of the local equations of `Z` glue to a unique global section of
`R¹ j_* μ_N`**, as soon as every point of `U` has a local equation around it. -/
theorem existsUnique_section_restrict_eq_localKummerClass (hNU : IsUnit ((N : ℕ) : Γ(U, ⊤)))
    {Z : Scheme.{u}} (i : Z ⟶ U) [IsClosedImmersion i]
    (hj : Set.range j.base ⊆ (Set.range i.base)ᶜ)
    (hcov : ∀ x : U, ∃ (V : U.Opens) (t : Γ(U, V)), x ∈ V ∧ IsLocalEquation i V t) :
    ∃! s : ToType ((kummerTarget j N).obj.obj (op ((opensToEtale U).obj ⊤))),
      ∀ (V : U.Opens) (t : Γ(U, V)) (ht : IsLocalEquation i V t),
        (kummerTarget j N).obj.map ((opensToEtale U).map (homOfLE le_top)).op s =
          localKummerClass j hN0 hN V t
            (isUnit_puncturedFunction j hj ht.diff_range_subset_basicOpen) := by
  let ι := {p : Σ V : U.Opens, Γ(U, V) // IsLocalEquation i p.1 p.2}
  let O : ι → U.Opens := fun p => p.1.1
  let sf : ∀ p : ι, ToType ((kummerTargetZariski j N).1.obj (op (O p))) := fun p =>
    localKummerClass j hN0 hN p.1.1 p.1.2
      (isUnit_puncturedFunction j hj p.2.diff_range_subset_basicOpen)
  have hcover : (⊤ : U.Opens) ≤ iSup O := by
    intro x _
    obtain ⟨V, t, hx, ht⟩ := hcov x
    exact Opens.mem_iSup.2 ⟨⟨⟨V, t⟩, ht⟩, hx⟩
  have hcompat : TopCat.Presheaf.IsCompatible (kummerTargetZariski j N).1 O sf := by
    intro p q
    show (kummerTarget j N).obj.map ((opensToEtale U).map (homOfLE inf_le_left)).op (sf p) =
      (kummerTarget j N).obj.map ((opensToEtale U).map (homOfLE inf_le_right)).op (sf q)
    rw [map_localKummerClass_restrict j hN0 hN inf_le_left p.1.2,
      map_localKummerClass_restrict j hN0 hN inf_le_right q.1.2]
    exact localKummerClass_eq_of_isLocalEquation j hN0 hN hNU (p.2.restrict inf_le_left)
      (q.2.restrict inf_le_right) _ _
  obtain ⟨s, hs, huniq⟩ := TopCat.Sheaf.existsUnique_gluing' (kummerTargetZariski j N) O ⊤
    (fun _ => homOfLE le_top) hcover sf hcompat
  exact ⟨s, fun V t ht => hs ⟨⟨V, t⟩, ht⟩, fun s' hs' => huniq s' fun p => hs' _ _ p.2⟩

/-- **The fundamental class of `Z` in `R¹ j_* μ_N`**: the unique global section of `R¹ j_* μ_N`
whose restriction to every open `V` with a local equation `t` of `Z` is the local Kummer class
`∂ t` (`Stacks.EtaleCohomology.Purity.existsUnique_section_restrict_eq_localKummerClass`). -/
def kummerDivisorSection (hNU : IsUnit ((N : ℕ) : Γ(U, ⊤))) {Z : Scheme.{u}} (i : Z ⟶ U)
    [IsClosedImmersion i] (hj : Set.range j.base ⊆ (Set.range i.base)ᶜ)
    (hcov : ∀ x : U, ∃ (V : U.Opens) (t : Γ(U, V)), x ∈ V ∧ IsLocalEquation i V t) :
    ToType ((kummerTarget j N).obj.obj (op ((opensToEtale U).obj ⊤))) :=
  (existsUnique_section_restrict_eq_localKummerClass j hN0 hN hNU i hj hcov).exists.choose

/-- **The fundamental class restricts to the local Kummer class of every local equation.** -/
theorem kummerDivisorSection_restrict (hNU : IsUnit ((N : ℕ) : Γ(U, ⊤))) {Z : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (hj : Set.range j.base ⊆ (Set.range i.base)ᶜ)
    (hcov : ∀ x : U, ∃ (V : U.Opens) (t : Γ(U, V)), x ∈ V ∧ IsLocalEquation i V t)
    (V : U.Opens) (t : Γ(U, V)) (ht : IsLocalEquation i V t) :
    (kummerTarget j N).obj.map ((opensToEtale U).map (homOfLE le_top)).op
        (kummerDivisorSection j hN0 hN hNU i hj hcov) =
      localKummerClass j hN0 hN V t
        (isUnit_puncturedFunction j hj ht.diff_range_subset_basicOpen) :=
  (existsUnique_section_restrict_eq_localKummerClass j hN0 hN hNU i hj hcov).exists.choose_spec
    V t ht

/-- **The fundamental class is characterised by its restrictions.** -/
theorem eq_kummerDivisorSection (hNU : IsUnit ((N : ℕ) : Γ(U, ⊤))) {Z : Scheme.{u}}
    (i : Z ⟶ U) [IsClosedImmersion i] (hj : Set.range j.base ⊆ (Set.range i.base)ᶜ)
    (hcov : ∀ x : U, ∃ (V : U.Opens) (t : Γ(U, V)), x ∈ V ∧ IsLocalEquation i V t)
    (s : ToType ((kummerTarget j N).obj.obj (op ((opensToEtale U).obj ⊤))))
    (hs : ∀ (V : U.Opens) (t : Γ(U, V)) (ht : IsLocalEquation i V t),
      (kummerTarget j N).obj.map ((opensToEtale U).map (homOfLE le_top)).op s =
        localKummerClass j hN0 hN V t
          (isUnit_puncturedFunction j hj ht.diff_range_subset_basicOpen)) :
    s = kummerDivisorSection j hN0 hN hNU i hj hcov :=
  (existsUnique_section_restrict_eq_localKummerClass j hN0 hN hNU i hj hcov).unique hs
    (kummerDivisorSection_restrict j hN0 hN hNU i hj hcov)

end KummerClass

end Stacks.EtaleCohomology.Purity

end
