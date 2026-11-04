module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.NoetherianSupportInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ColimitDerivedKilling
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.SupportedSubsheafDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositeDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic

/-!
# The local killing statement at a maximal point, from two local inputs

This file proves the local statement `AlgebraicGeometry.Scheme.GenericPointSupportKilling` of the
dévissage of Travaux de Gabber, Exposé XVIII-A, Lemma 2.2, from two inputs, each a statement
about the local scheme at the maximal point `η` of `T = X ∖ U`:

* `AlgebraicGeometry.Scheme.PuncturedStalkVanishing n`: the stalks at geometric points over `η` of
  `R^m j_* 𝓖` vanish for `m ≥ 2 dim 𝒪_{X,η}`, for `j : U ⟶ X` and `𝓖` killed by `n`. These stalks
  are the cohomology of the punctured spectrum of the strict henselization of `𝒪_{X,η}` (Stacks
  03Q9), and the input is the punctured bound of Exposé XVIII-A, Theorem 1.1.
* `AlgebraicGeometry.Scheme.LocalSectionsAtPoint n`: a functor `Ψ` of "sections over the local
  scheme at `η`", the pointwise filtered colimit of the sections over the open neighbourhoods of
  `η` (in the source, `Γ(Spec 𝒪_{X,η}, -)` of the inverse image), whose derived functors vanish
  above `c(η)` on sheaves killed by `n` supported in `T`, and in every degree on sheaves supported
  in `T ∖ {η}`.

**The argument** is the source's computation of `H^i_η(Spec 𝒪_{X,η}, 𝓕)` by the spectral sequence
`H^p(κ(η), R^q i^! 𝓕)`. The functor `Ψ ∘ 𝒦_U` (with `𝒦_U` the subsheaf of sections supported in
`T`, which preserves injectives) has `R^i(Ψ ∘ 𝒦_U)(𝓕) = 0` for `i > c(η) + 2 dim 𝒪_{X,η}` by the
antidiagonal vanishing of the Grothendieck spectral sequence: the sheaves `R^q 𝒦_U(𝓕)` are killed
by `n` and supported in `T`, and for `q > 2 dim 𝒪_{X,η}` also have zero stalks over `η`, being
quotients of `R^{q-1} j_*(𝓕|_U)` there. Since `Ψ ∘ 𝒦_U` is the pointwise filtered colimit of the
functors `Γ_{V, V ⊓ U} = Γ(V, 𝒦_U(-))`, every class of `R^iΓ_{X, U}(𝓕)` dies in some
`R^iΓ_{V, V ⊓ U}(𝓕)` (`CategoryTheory.exists_rightDerived_app_eq_zero_of_isZero`).

## Main definitions

* `AlgebraicGeometry.Scheme.PuncturedStalkVanishing`
* `AlgebraicGeometry.Scheme.LocalSectionsData` and `AlgebraicGeometry.Scheme.LocalSectionsAtPoint`

## Main results

* `AlgebraicGeometry.Scheme.genericPointSupportKilling_of_localInputs`
* `AlgebraicGeometry.Scheme.localToGlobalVanishingBound_of_localInputs`: Exposé XVIII-A,
  Lemma 2.2 from the two inputs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-! ### Two inequalities in `WithBot ℕ∞` -/

/-- In `WithBot ℕ∞`, `x < q + 1` implies `x ≤ q`. -/
theorem le_natCast_of_lt_natCast_succ {x : WithBot ℕ∞} {q : ℕ}
    (h : x < ((q + 1 : ℕ) : WithBot ℕ∞)) : x ≤ (q : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact absurd h (not_lt.2 (by exact_mod_cast le_top))
    | coe m =>
      have : m < q + 1 := by exact_mod_cast h
      exact_mod_cast Nat.lt_succ_iff.1 this

/-- In `WithBot ℕ∞`, if `c + d < i` and `q ≤ d`, then `c < i - q`, with `i - q` the truncated
subtraction of natural numbers. -/
theorem lt_natCast_sub_of_add_lt {c d : WithBot ℕ∞} {q i : ℕ}
    (h : c + d < (i : WithBot ℕ∞)) (hq : (q : WithBot ℕ∞) ≤ d) :
    c < ((i - q : ℕ) : WithBot ℕ∞) := by
  induction c using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe c' =>
  induction d using WithBot.recBotCoe with
  | bot => exact absurd hq (not_le.2 (WithBot.bot_lt_coe _))
  | coe d' =>
  rw [← WithBot.coe_add] at h
  have ht : c' + d' ≠ ⊤ := fun e => by simp [e] at h
  lift c' to ℕ using fun e => ht (by simp [e])
  lift d' to ℕ using fun e => ht (by simp [e])
  have h' : c' + d' < i := by exact_mod_cast h
  have hq' : q ≤ d' := by exact_mod_cast hq
  exact WithBot.coe_lt_coe.2 (Nat.cast_lt.2 (by omega))

/-! ### The two local inputs -/

/-- **The punctured input**: for a Noetherian scheme `X` on which `n` is invertible, an open `U`,
a maximal point `η` of `X ∖ U` and an abelian sheaf `𝓖` on `U_ét` killed by `n`, the stalk of
`R^m j_* 𝓖` at every geometric point over `η` vanishes for `m ≥ 2 dim 𝒪_{X,η}`. -/
def PuncturedStalkVanishing (n : ℕ) : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X], IsUnit (n : Γ(X, ⊤)) →
    ∀ (U : X.Opens) (η : X), η ∉ U → (∀ x : X, η ∈ closure ({x} : Set X) → x ∉ U → x = η) →
      ∀ G : Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1},
        (∀ (T : U.toScheme.Etale) (x : G.obj.obj (op T)), n • x = 0) →
          ∀ m : ℕ, 2 * ringKrullDim (X.presheaf.stalk η) ≤ m →
            ∀ s : GeometricPoint X, s.hom (IsLocalRing.closedPoint s.residueField) = η →
              IsZero ((Stacks.EtaleCohomology.smallEtaleStalkAb s.hom).obj
                (((Stacks.EtaleCohomology.smallEtalePushforwardAb U.ι).rightDerived m).obj G))

/-- **Sections over the local scheme at `η`**: a functor `Ψ` on abelian sheaves on `X_ét` with a
cocone from the sections over the open neighbourhoods of `η` which is a colimit pointwise, whose
right derived functors vanish above `c` on sheaves killed by `n` with zero stalks over `U`, and in
every degree on sheaves with zero stalks over `U` and over `η`. -/
structure LocalSectionsData {X : Scheme.{u}} (U : X.Opens) (η : X) (n : ℕ) (c : WithBot ℕ∞) where
  /-- The functor of sections over the local scheme. -/
  Ψ : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}
  [additive : Ψ.Additive]
  /-- The cocone from the sections over the open neighbourhoods of `η`. -/
  θ : ∀ V : X.Opens, η ∈ V →
    ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op ((opensToEtale X).obj V)) ⟶ Ψ)
  comp : ∀ (V V' : X.Opens) (hV : η ∈ V) (hV' : η ∈ V') (h : V' ≤ V),
    (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((opensToEtale X).map (homOfLE h)).op ≫ θ V' hV' = θ V hV
  surj : ∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (y : Ψ.obj G),
    ∃ (V : X.Opens) (hV : η ∈ V) (x : G.obj.obj (op ((opensToEtale X).obj V))),
      (θ V hV).app G x = y
  ker : ∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (V : X.Opens) (hV : η ∈ V)
    (x : G.obj.obj (op ((opensToEtale X).obj V))), (θ V hV).app G x = 0 →
      ∃ (V' : X.Opens) (h : V' ≤ V), η ∈ V' ∧
        G.obj.map ((opensToEtale X).map (homOfLE h)).op x = 0
  vanish : ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
    (∀ (T : X.Etale) (x : G.obj.obj (op T)), n • x = 0) →
      (∀ s : GeometricPoint X, s.hom (IsLocalRing.closedPoint s.residueField) ∈ U →
        IsZero ((Stacks.EtaleCohomology.smallEtaleStalkAb s.hom).obj G)) →
        ∀ p : ℕ, c < p → IsZero ((Ψ.rightDerived p).obj G)
  vanish' : ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
    (∀ s : GeometricPoint X, (s.hom (IsLocalRing.closedPoint s.residueField) ∈ U ∨
        s.hom (IsLocalRing.closedPoint s.residueField) = η) →
      IsZero ((Stacks.EtaleCohomology.smallEtaleStalkAb s.hom).obj G)) →
      ∀ p : ℕ, IsZero ((Ψ.rightDerived p).obj G)

attribute [instance] LocalSectionsData.additive

/-- **The local-sections input** at every maximal point of the complement of an open subscheme of
a Noetherian scheme. -/
def LocalSectionsAtPoint (n : ℕ) : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X], IsUnit (n : Γ(X, ⊤)) →
    ∀ (U : X.Opens) (η : X), η ∉ U → (∀ x : X, η ∈ closure ({x} : Set X) → x ∉ U → x = η) →
      ∀ c : WithBot ℕ∞, IsTorsionVanishingBound (Spec (.of (X.residueField η))) n c →
        Nonempty (LocalSectionsData U η n c)

/-! ### The reduction -/

variable {n : ℕ}

/-- Sections over an open, as a functor of abelian sheaves on `X_ét`. -/
abbrev opensSections {X : Scheme.{u}} (V : X.Opens) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op ((opensToEtale X).obj V))

/-- Restriction of sections to a smaller open. -/
abbrev opensSectionsRestrict {X : Scheme.{u}} {V V' : X.Opens} (h : V' ≤ V) :
    opensSections V ⟶ opensSections V' :=
  (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
    ((opensToEtale X).map (homOfLE h)).op

/-- Restricting sections from `V` to `V'` and then to `V''` is restricting from `V` to `V''`. -/
theorem opensSectionsRestrict_comp {X : Scheme.{u}} {V V' V'' : X.Opens} (h : V' ≤ V)
    (h' : V'' ≤ V') :
    opensSectionsRestrict h ≫ opensSectionsRestrict h' = opensSectionsRestrict (h'.trans h) := by
  rw [← Functor.map_comp, ← op_comp, ← Functor.map_comp]
  rfl

/-- **The colimit step**: if `R^i(Ψ ∘ 𝒦_U)(𝓕) = 0` then every class of `R^iΓ_{X,U}(𝓕)` dies in some
`R^iΓ_{V, V ⊓ U}(𝓕)`, `V` an open neighbourhood of `η`. -/
theorem exists_opensSupport_eq_zero_of_isZero {X : Scheme.{u}} (U : X.Opens) (η : X)
    {c : WithBot ℕ∞} (D : LocalSectionsData U η n c)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ)
    (hvan : IsZero (((supportedSubsheaf U ⋙ D.Ψ).rightDerived i).obj F))
    (ξ : ((opensSupport (le_top : U ≤ ⊤)).rightDerived i).obj F) :
    ∃ V : X.Opens, η ∈ V ∧
      (NatTrans.rightDerived (opensSupportRestrict (le_top : U ≤ ⊤)
        (inf_le_left : V ⊓ U ≤ V) le_top inf_le_right) i).app F ξ = 0 := by
  let 𝒦 := supportedSubsheaf U
  -- the directed set of open neighbourhoods of `η`, ordered by reverse inclusion
  let ι := (Subtype fun V : X.Opens => η ∈ V)ᵒᵈ
  have : IsDirected ι (· ≤ ·) := ⟨fun a b =>
    ⟨OrderDual.toDual ⟨(OrderDual.ofDual a).1 ⊓ (OrderDual.ofDual b).1,
      ⟨(OrderDual.ofDual a).2, (OrderDual.ofDual b).2⟩⟩,
      (inf_le_left : (OrderDual.ofDual a).1 ⊓ (OrderDual.ofDual b).1 ≤ _),
      (inf_le_right : (OrderDual.ofDual a).1 ⊓ (OrderDual.ofDual b).1 ≤ _)⟩⟩
  have : Nonempty ι := ⟨OrderDual.toDual ⟨⊤, trivial⟩⟩
  let Φ : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
    fun k => 𝒦 ⋙ opensSections (OrderDual.ofDual k).1
  let sₖ : ∀ k : ι, 𝒦 ⋙ opensSections ⊤ ⟶ Φ k := fun k =>
    Functor.whiskerLeft 𝒦 (opensSectionsRestrict (le_top : (OrderDual.ofDual k).1 ≤ ⊤))
  let ρ : ∀ {k l : ι}, k ≤ l → (Φ k ⟶ Φ l) := fun {k l} h =>
    Functor.whiskerLeft 𝒦 (opensSectionsRestrict
      (show (OrderDual.ofDual l).1 ≤ (OrderDual.ofDual k).1 from h))
  let θ' : ∀ k : ι, Φ k ⟶ 𝒦 ⋙ D.Ψ := fun k =>
    Functor.whiskerLeft 𝒦 (D.θ (OrderDual.ofDual k).1 (OrderDual.ofDual k).2)
  have hsρ : ∀ {k l : ι} (h : k ≤ l), sₖ k ≫ ρ h = sₖ l := fun {k l} h => by
    simp only [sₖ, ρ]
    rw [← Functor.whiskerLeft_comp, opensSectionsRestrict_comp]
  have hρθ : ∀ {k l : ι} (h : k ≤ l), ρ h ≫ θ' l = θ' k := fun {k l} h => by
    simp only [ρ, θ', ← Functor.whiskerLeft_comp]
    rw [D.comp]
  have hsurj : ∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (y : (𝒦 ⋙ D.Ψ).obj G), ∃ (k : ι) (x : (Φ k).obj G), (θ' k).app G x = y := by
    intro G y
    obtain ⟨V, hV, x, hx⟩ := D.surj (𝒦.obj G) y
    exact ⟨OrderDual.toDual ⟨V, hV⟩, x, hx⟩
  have hker : ∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (k : ι)
      (x : (Φ k).obj G), (θ' k).app G x = 0 → ∃ (l : ι) (h : k ≤ l), (ρ h).app G x = 0 := by
    intro G k x hx
    obtain ⟨V', h, hV', hz⟩ := D.ker (𝒦.obj G) _ (OrderDual.ofDual k).2 x hx
    exact ⟨OrderDual.toDual ⟨V', hV'⟩, h, hz⟩
  let α₀ := opensSupportIsoSupportedSubsheaf (U := U) (le_top : U ≤ ⊤) (le_refl U)
    (inf_le_right : ⊤ ⊓ U ≤ U)
  obtain ⟨k, hk⟩ := exists_rightDerived_app_eq_zero_of_isZero (𝒦 ⋙ opensSections ⊤) Φ
    (𝒦 ⋙ D.Ψ) sₖ ρ θ' hsρ hρθ hsurj hker F i hvan ((NatTrans.rightDerived α₀.hom i).app F ξ)
  let V := (OrderDual.ofDual k).1
  let αV := opensSupportIsoSupportedSubsheaf (U := U) (inf_le_left : V ⊓ U ≤ V)
    (inf_le_right : V ⊓ U ≤ U) (le_refl (V ⊓ U))
  have sq := opensSupportRestrict_comp_opensSupportIsoSupportedSubsheaf_hom (U := U)
    (le_top : U ≤ ⊤) (le_refl U) (inf_le_right : ⊤ ⊓ U ≤ U) (inf_le_left : V ⊓ U ≤ V)
    (inf_le_right : V ⊓ U ≤ U) (le_refl (V ⊓ U)) (le_top : V ≤ ⊤) (inf_le_right : V ⊓ U ≤ U)
  refine ⟨V, (OrderDual.ofDual k).2, ?_⟩
  have hiso : IsIso ((NatTrans.rightDerived αV.hom i).app F) :=
    Iso.isIso_hom ((Stacks.Cohomology.CechDelta.rightDerivedIsoOfIso αV i).app F)
  apply ((ConcreteCategory.isIso_iff_bijective _).1 hiso).1
  rw [map_zero, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
    ← NatTrans.rightDerived_comp, sq, NatTrans.rightDerived_comp, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  exact hk


/-- **The local killing statement from the two local inputs.** -/
theorem genericPointSupportKilling_of_localInputs (h₁ : PuncturedStalkVanishing.{u} n)
    (h₂ : LocalSectionsAtPoint.{u} n) : GenericPointSupportKilling.{u} n := by
  intro X _ hn U η hηU hmax c hc F hF i hi ξ
  obtain ⟨D⟩ := h₂ X hn U η hηU hmax c hc
  let 𝒦 := supportedSubsheaf U
  let δ := ringKrullDim (X.presheaf.stalk η)
  have hδ : 0 ≤ 2 * δ := mul_nonneg (by norm_num) ringKrullDim_nonneg_of_nontrivial
  -- the vanishing of `R^i(Ψ ∘ 𝒦_U)(𝓕)`
  have hvan : IsZero (((𝒦 ⋙ D.Ψ).rightDerived i).obj F) := by
    refine Stacks.CompositeDegreeVanishing.isZero_rightDerived_comp_obj_of_isZero 𝒦 D.Ψ F i
      fun q hq => ?_
    let G := (𝒦.rightDerived q).obj F
    have hGn : ∀ (T : X.Etale) (x : G.obj.obj (op T)), n • x = 0 :=
      (forall_nsmul_eq_zero_iff_nsmul_id_eq_zero G).2 (nsmul_id_obj_eq_zero (𝒦.rightDerived q)
        ((forall_nsmul_eq_zero_iff_nsmul_id_eq_zero F).1 hF))
    have hGU : ∀ s : GeometricPoint X, s.hom (IsLocalRing.closedPoint s.residueField) ∈ U →
        IsZero ((Stacks.EtaleCohomology.smallEtaleStalkAb s.hom).obj G) := fun s hs =>
      isZero_stalk_rightDerived_supportedSubsheaf_of_mem U F q s.hom hs
    by_cases hq' : 2 * δ < (q : WithBot ℕ∞)
    · obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := by
        rcases q with _ | m
        · exact absurd hq' (not_lt.2 (by simpa using hδ))
        · exact ⟨m, rfl⟩
      refine D.vanish' G (fun s hs => ?_) _
      rcases hs with hs | hs
      · exact hGU s hs
      · refine isZero_stalk_rightDerived_supportedSubsheaf_succ U F m s.hom ?_
        exact h₁ X hn U η hηU hmax _ (fun T x => hF _ x) m
          (le_natCast_of_lt_natCast_succ hq') s hs
    · exact D.vanish G hGn hGU _ (lt_natCast_sub_of_add_lt hi (not_lt.1 hq'))
  exact exists_opensSupport_eq_zero_of_isZero U η D F i hvan ξ

/-- **Exposé XVIII-A, Lemma 2.2, from the two local inputs.** -/
theorem localToGlobalVanishingBound_of_localInputs (h₁ : PuncturedStalkVanishing.{u} n)
    (h₂ : LocalSectionsAtPoint.{u} n) : LocalToGlobalVanishingBound.{u} n :=
  localToGlobalVanishingBound_of_genericPointSupportKilling
    (genericPointSupportKilling_of_localInputs h₁ h₂)

end AlgebraicGeometry.Scheme

end
