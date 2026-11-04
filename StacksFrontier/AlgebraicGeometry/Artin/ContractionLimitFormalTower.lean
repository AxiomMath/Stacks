module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitFormalRing
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitFormalDictionary

/-!
# The ring map of a morphism through the completion of an affine object

In the last part of the proof of Stacks 0GI5, a continuous ring map `φ : B → A^∧` gives the
morphism `V_{/Z} ≅ Spf A^∧ ⟶ Spf B` of the dictionary
`AlgebraicGeometry.Artin.FormalDictionary.continuousHomEquiv`. Composing with the morphism into
`V_{/Z}` of an algebraic space `X ⟶ V` whose image lies in `Z` gives a morphism `X ⟶ Spf B`. When
`X ⟶ V` factors through a quotient stage `Spec (A^∧ ⧸ I^{n+1} A^∧)`, its ring map
`AlgebraicGeometry.Artin.FormalRing.formalRingHom` is `B → A^∧ → A^∧ ⧸ I^{n+1} A^∧ → Γ(X, 𝒪_X)`.
This is what makes the ring maps of the source compatible with the morphisms of the source.

## Main definitions

* `AlgebraicGeometry.Artin.FormalRing.toCompletion`: the morphism `X ⟶ Y_{/T}` of a morphism
  `X ⟶ Y` whose image lies in `T`.

## Main results

* `AlgebraicGeometry.Artin.FormalRing.toCompletion_comp_completionIsoFormalSpectrum_hom`: the
  value of `V_{/Z} ≅ Spf A^∧` on a morphism through a quotient stage.
* `AlgebraicGeometry.Artin.FormalRing.formalRingHom_toCompletion_comp_continuousHomEquiv`: the
  ring map of `X ⟶ V_{/Z} ⟶ Spf B`.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.FormalRing

open Space FormalSpace FormalDictionary

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section ToCompletion

variable {X X' Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The morphism `X ⟶ Y_{/T}` of presheaves of a morphism `m : X ⟶ Y` whose image lies in `T`,
before sheafifying. -/
def toCompletionPre (m : X ⟶ Y) (T : Set (points B S hS Y))
    (h : ∀ x, pointsMap B S hS X m x ∈ T) :
    X ⋙ uliftFunctor.{u + 1} ⟶ (completionSubfunctor B S hS Y T).toFunctor :=
  ({ app := fun _ => ↾fun x => ⟨x, fun _ => Set.mem_univ _⟩
     naturality := fun _ _ _ => rfl } :
      X ⋙ uliftFunctor.{u + 1} ⟶ (completionSubfunctor B S hS X Set.univ).toFunctor) ≫
    completionSubfunctorRestrict B S hS m Set.univ T (fun x _ => h x)

/-- The morphism `X ⟶ Y_{/T}` of a morphism `m : X ⟶ Y` whose image lies in `T`. -/
def toCompletion (m : X ⟶ Y) (T : Set (points B S hS Y))
    (h : ∀ x, pointsMap B S hS X m x ∈ T) :
    sheafifiedULift B S hS X ⟶ completionSheaf B S hS Y T :=
  (fppfSheafification B S hS).map (toCompletionPre m T h)

/-- The morphism `X' ⟶ Y_{/T}` of `m' ≫ m` is `m'` followed by the morphism `X ⟶ Y_{/T}` of `m`. -/
theorem toCompletion_comp_left (m' : X' ⟶ X) (m : X ⟶ Y) (T : Set (points B S hS Y))
    (h : ∀ x, pointsMap B S hS X m x ∈ T) (h' : ∀ x, pointsMap B S hS X' (m' ≫ m) x ∈ T) :
    toCompletion (m' ≫ m) T h' = sheafifiedULiftMap B S hS m' ≫ toCompletion m T h := by
  have e : toCompletionPre (m' ≫ m) T h' =
      Functor.whiskerRight m' uliftFunctor.{u + 1} ≫ toCompletionPre m T h := by
    ext U x
    rfl
  rw [toCompletion, e, Functor.map_comp, sheafifiedULiftMap_eq_map]
  rfl

/-- The morphism `X ⟶ Y_{/T}` of `m` followed by the restriction `Y_{/T} ⟶ Y'_{/T'}` along `g`
is the morphism `X ⟶ Y'_{/T'}` of `m ≫ g`. -/
theorem toCompletion_comp_completionSheafRestrict (m : X ⟶ Y) (g : Y ⟶ Y')
    (T : Set (points B S hS Y)) (T' : Set (points B S hS Y'))
    (h : ∀ x, pointsMap B S hS X m x ∈ T) (hT : T ⊆ pointsMap B S hS Y g ⁻¹' T')
    (h' : ∀ x, pointsMap B S hS X (m ≫ g) x ∈ T') :
    toCompletion m T h ≫ completionSheafRestrict B S hS g T T' hT =
      toCompletion (m ≫ g) T' h' := by
  have e : toCompletionPre m T h ≫ completionSubfunctorRestrict B S hS g T T' hT =
      toCompletionPre (m ≫ g) T' h' := by
    ext U x
    rfl
  rw [toCompletion, toCompletion, ← e, Functor.map_comp]
  rfl

end ToCompletion

/-- The section over `V` of the inverse of `sheafifiedULift (yoneda V) ≅ sheafifiedYoneda V` is
the image of `𝟙 V` under the sheafification map. -/
theorem sectionEquiv_sheafifiedULiftIsoYoneda_inv (V : BigFppfOver B S hS) :
    Sheaf.sectionEquiv (BigFppfOver.topology B S hS) (sheafifiedULiftIsoYoneda V).inv =
      ((BigFppfOver.topology B S hS).toSheafify
        (yoneda.obj V ⋙ uliftFunctor.{u + 1})).app (op V) ⟨𝟙 V⟩ := by
  have h : toSheafify (BigFppfOver.topology B S hS) (yoneda.obj V ⋙ uliftFunctor.{u + 1}) ≫
      (sheafifiedULiftIsoYoneda V).inv.hom =
      (BigFppfOver.topology B S hS).toSheafify (yoneda.obj V ⋙ uliftFunctor.{u + 1}) :=
    (Iso.comp_inv_eq ((sheafToPresheaf (BigFppfOver.topology B S hS)
      (Type (u + 1))).mapIso (sheafifiedULiftIsoYoneda V))).mpr
        (toSheafify_plusPlusIsoSheafify_hom (BigFppfOver.topology B S hS) (Type (u + 1))
          (yoneda.obj V ⋙ uliftFunctor.{u + 1})).symm
  show (toSheafify (BigFppfOver.topology B S hS) (yoneda.obj V ⋙ uliftFunctor.{u + 1}) ≫
    (sheafifiedULiftIsoYoneda V).inv.hom).app (op V) ⟨𝟙 V⟩ = _
  rw [h]
  rfl

/-- The section of `Y_{/T}` over `N` given by `t : N ⟶ Y` is the morphism `toCompletion` of
`t`, read through `sheafifiedULift (yoneda N) ≅ sheafifiedYoneda N`. -/
theorem sectionEquiv_toCompletion {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {N : BigFppfOver B S hS}
    (t : yoneda.obj N ⟶ Y) (T : Set (points B S hS Y)) (h : ∀ x, pointsMap B S hS _ t x ∈ T)
    (ht : HasImageIn B S hS Y T N (t.app (op N) (𝟙 N))) :
    Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        ((sheafifiedULiftIsoYoneda N).inv ≫ toCompletion t T h) =
      presheafSection B S hS (t.app (op N) (𝟙 N)) ht := by
  rw [Sheaf.sectionEquiv_comp, sectionEquiv_sheafifiedULiftIsoYoneda_inv]
  have hnat := congrArg (fun φ => φ.app (op N) ⟨𝟙 N⟩)
    ((BigFppfOver.topology B S hS).toSheafify_naturality (toCompletionPre t T h))
  refine Eq.trans ?_ (hnat.symm.trans ?_)
  · rfl
  · rfl

section Dictionary

/-- The `I`-adic topology on the `I`-adic completion `AdicCompletion I A` of `A`. -/
local instance instTopologicalSpaceAdicCompletion'' {A : Type u} [CommRing A] (I : Ideal A) :
    TopologicalSpace (AdicCompletion I A) :=
  I.adicModuleTopology (AdicCompletion I A)

variable {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
  {I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
  {Z : Set (Space.points B S hS (yoneda.obj V))}
  (hZI : ∀ x, x ∈ Z ↔ Space.pointsToScheme B S hS V x ∈
    ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
      (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))

include hZI in
/-- **The value of `V_{/Z} ≅ Spf A^∧` on a morphism through a quotient stage**: for
`s : X ⟶ Spec (A^∧ ⧸ I^{n+1})`, the morphism `X ⟶ V_{/Z} ≅ Spf A^∧` of `X ⟶ V` is the inclusion
of the quotient stage. -/
theorem toCompletion_comp_completionIsoFormalSpectrum_hom {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (n : ℕ) (s : X ⟶ yoneda.obj (powStage V I n))
    (h : ∀ x, pointsMap B S hS X (s ≫ yoneda.map (powStageToV V I n)) x ∈ Z) :
    toCompletion (s ≫ yoneda.map (powStageToV V I n)) Z h ≫
        (completionIsoFormalSpectrum hZI).hom =
      sheafifiedULiftMap B S hS s ≫ (sheafifiedULiftIsoYoneda (powStage V I n)).hom ≫
        powStageIncl V I n := by
  have h₀ : ∀ x, pointsMap B S hS _ (yoneda.map (powStageToV V I n)) x ∈ Z := by
    have hh := hasImageIn_powStageToV hZI n
    rw [Space.hasImageIn_iff_range_subset] at hh
    have e : yonedaEquiv.symm (powStageToV V I n) = yoneda.map (powStageToV V I n) :=
      yonedaEquiv.injective (by rw [Equiv.apply_symm_apply, yonedaEquiv_yoneda_map])
    rw [e] at hh
    exact fun x => hh ⟨x, rfl⟩
  rw [toCompletion_comp_left s (yoneda.map (powStageToV V I n)) Z h₀, Category.assoc]
  congr 1
  rw [← Iso.inv_comp_eq, ← Category.assoc]
  have hsec := sectionEquiv_toCompletion (yoneda.map (powStageToV V I n)) Z h₀
    (by simpa using hasImageIn_powStageToV hZI n)
  have hval := sectionEquiv_symm_presheafSection_comp_completionIsoFormalSpectrum_hom hZI
    (powStageToV V I n) (hasImageIn_powStageToV hZI n) n (𝟙 _) (Category.id_comp _)
  rw [← Equiv.eq_symm_apply] at hsec
  rw [hsec]
  refine (congrArg (· ≫ (completionIsoFormalSpectrum hZI).hom) ?_).trans
    (hval.trans (by rw [CategoryTheory.Functor.map_id, Category.id_comp]))
  congr 2

variable (I) in
/-- The ring map `A^∧ ⟶ A^∧ ⧸ I^{n+1} A^∧ ≅ Γ(Spec (A^∧ ⧸ I^{n+1} A^∧), 𝒪)` of a quotient stage. -/
def powStageRingHom' (n : ℕ) :
    AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+*
      Γ((BigFppfOver.toScheme B S hS).obj (powStage V I n), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸
    (adicCompletionPowStageIdeal I I.fg_of_isNoetherianRing n).1))).inv.hom.comp
    (Ideal.Quotient.mk _)

variable {Bt : Type u} [CommRing Bt] [TopologicalSpace Bt] [IsTopologicalRing Bt]
  [IsLinearTopology Bt Bt] (hB : TopologicalRing.IsWeaklyAdmissible Bt)
  {DB : QuotientSystem B S hS Bt}

include hB in
/-- For a continuous ring map `φ : B → A^∧` with `B` weakly admissible, every weak ideal of
definition `K` of `A^∧` contains the image of a weak ideal of definition `J` of `B`, that is,
`J ≤ φ⁻¹ K`. -/
theorem exists_weakIdeal_le_comap (φ : ContinuousHom DB (completionQuotientSystem V I))
    (K : { J : Ideal (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) //
      TopologicalRing.IsWeakIdealOfDefinition J }) :
    ∃ J : { J : Ideal Bt // TopologicalRing.IsWeakIdealOfDefinition J },
      J.1 ≤ Ideal.comap φ.toRingHom K.1 := by
  obtain ⟨J₀, hJ₀⟩ := hB.1
  refine ⟨⟨J₀ ⊓ Ideal.comap φ.toRingHom K.1, ?_, fun x hx => hJ₀.2 x (Ideal.mem_inf.mp hx).1⟩,
    inf_le_right⟩
  show IsOpen ((J₀ : Set Bt) ∩ φ.toRingHom ⁻¹' (K.1 : Set _))
  exact hJ₀.1.inter (K.2.1.preimage φ.continuous)

include hZI in
/-- **The ring map of `X ⟶ V_{/Z} ⟶ Spf B`** for `X ⟶ V` factoring through the quotient stage
`s : X ⟶ Spec (A^∧ ⧸ I^{n+1} A^∧)`, and a continuous `φ : B ⟶ A^∧`: it is
`B ⟶ A^∧ ⟶ A^∧ ⧸ I^{n+1} A^∧ ⟶ Γ(X, 𝒪_X)`. -/
theorem formalRingHom_toCompletion_comp_continuousHomEquiv (X : AlgebraicSpaces B S hS)
    (hX : IsQuasiCompactSpace B S hS X.1) (n : ℕ) (s : X.1 ⟶ yoneda.obj (powStage V I n))
    (h : ∀ x, pointsMap B S hS X.1 (s ≫ yoneda.map (powStageToV V I n)) x ∈ Z)
    (φ : ContinuousHom DB (completionQuotientSystem V I)) :
    formalRingHom hB X hX (toCompletion (s ≫ yoneda.map (powStageToV V I n)) Z h ≫
        continuousHomEquiv hZI hB φ) =
      (pullbackRingHom B (powStage V I n) (ObjectProperty.homMk s)).comp
        ((powStageRingHom' I n).comp φ.toRingHom) := by
  let K := adicCompletionPowStageIdeal I I.fg_of_isNoetherianRing n
  obtain ⟨J, hJ⟩ := exists_weakIdeal_le_comap hB φ K
  let sm : powStage V I n ⟶ stageObj DB (OrderDual.toDual J) :=
    (BigAffineFppf.inclusion B S hS).map (φ.stageMap J K hJ)
  have hspec : powStageIncl V I n ≫ formalSpectrumMap hB φ =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map sm ≫
        stageIncl DB (OrderDual.toDual J) :=
    formalSpectrumMap_spec hB φ J K hJ
  have hfac : IsStageFactor X (toCompletion (s ≫ yoneda.map (powStageToV V I n)) Z h ≫
      continuousHomEquiv hZI hB φ) (OrderDual.toDual J) (s ≫ yoneda.map sm) := by
    unfold IsStageFactor
    rw [continuousHomEquiv_apply, ← Category.assoc (toCompletion _ Z h),
      toCompletion_comp_completionIsoFormalSpectrum_hom hZI n s h, Category.assoc,
      Category.assoc, hspec, sheafifiedULiftMap_comp, Category.assoc,
      sheafifiedULiftMap_yoneda_comp_iso_assoc]
  rw [formalRingHom_eq hB X hX hfac]
  refine RingHom.ext fun b => ?_
  refine (pullbackRingHom_homMk_comp X s sm _).trans ?_
  refine congrArg (pullbackRingHom B _ (ObjectProperty.homMk s)) ?_
  show (Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 φ.toRingHom hJ))).appTop
      ((Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk _ b)) =
    (Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk _ (φ.toRingHom b))
  have := congrArg (fun ψ => ψ.hom (Ideal.Quotient.mk _ b))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.quotientMap K.1 φ.toRingHom hJ)))
  exact this.symm.trans (congrArg (Scheme.ΓSpecIso _).inv.hom (Ideal.quotientMap_mk (H := hJ)))

end Dictionary

end AlgebraicGeometry.Artin.FormalRing

end
