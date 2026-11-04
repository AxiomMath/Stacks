module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.LipDCechPrimitive

/-!
# Local primitives glue for the direct image of the structure sheaf

Let `V` be the vanishing situation of a normal modification `Y ⟶ Spec(A)`, let `π : Y ⟶ X` be a
surjective morphism, and let `W ⊆ X` be an open whose inverse image in `Y` is the part of `Y`
over the punctured spectrum of `A`. For an injective resolution `I` of `π_* 𝒪_Y` on `X`, a cocycle
of `Γ(X, I¹)` which has primitives on the members of an open cover of `X`, one of which is `W`,
has a global primitive. This is
`AlgebraicGeometry.PuncturedRestriction.exists_d_eq_of_local_primitives` read through `π`; the
polar lemma is applied on `Y`.

## Main results

* `AlgebraicGeometry.PuncturedRestriction.exists_d_eq_of_local_primitives_pushforward`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.PuncturedRestriction

/-- Sections of an abelian sheaf on a scheme over an open with no points agree. -/
theorem eq_of_isEmpty' {X : Scheme.{u}} {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {U : X.Opens} (hU : ∀ x : X, x ∉ U) (a b : ToType (G.obj.obj (op U))) : a = b := by
  have hbot : U = ⨆ i : PEmpty.{u + 1}, (PEmpty.elim i : X.Opens) := by
    ext x
    simp only [Opens.iSup_def, Set.iUnion_of_empty, SetLike.mem_coe]
    exact ⟨fun hx => (hU x hx).elim, fun hx => hx.elim⟩
  exact TopCat.Sheaf.eq_of_locally_eq' (F := (⟨G.obj, G.property⟩ :
      TopCat.Sheaf AddCommGrpCat.{u} X.carrier)) (fun i : PEmpty.{u + 1} => PEmpty.elim i) U
    (fun i => PEmpty.elim i) hbot.le a b (fun i => PEmpty.elim i)

section Pushforward

variable (V : VanishingSituation.{u}) {X : Scheme.{u}} (π : V.X ⟶ X) [Surjective π]

local notation "𝒪" => structureSheafRing X.toLocallyRingedSpace.toRingedSpace

/-- The direct image `π_* 𝒪_Y`. -/
abbrev pushUnit :
    SheafOfModules.{u} (structureSheafRing X.toLocallyRingedSpace.toRingedSpace) :=
  (Scheme.Modules.pushforward π).obj (SheafOfModules.unit V.X.ringCatSheaf)

/-- A section of `π_* 𝒪_Y` over `U` as a section of `𝒪_Y` over `π⁻¹(U)`. -/
def toΓY {U : X.Opens} (s : (secF 𝒪 U).obj (pushUnit V π)) : Γ(V.X, π ⁻¹ᵁ U) := s

omit [Surjective π] in
/-- `toΓY` commutes with restriction. -/
theorem toΓY_res {U U' : X.Opens} (h : U' ≤ U) (s : (secF 𝒪 U).obj (pushUnit V π)) :
    toΓY V π ((secRestrict 𝒪 h).app _ s) =
      V.X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π h)).op (toΓY V π s) := rfl

omit [Surjective π] in
/-- `toΓY` is additive. -/
theorem toΓY_sub {U : X.Opens} (s t : (secF 𝒪 U).obj (pushUnit V π)) :
    toΓY V π (s - t) = toΓY V π s - toΓY V π t := rfl

/-- A section of `π_* 𝒪_Y` over `W`, with `π⁻¹(W)` containing the generic point of `Y`, as a
rational function on `Y`. -/
def toFunctionField [IsIntegral V.X] {W : X.Opens} (hW : genericPoint V.X ∈ π ⁻¹ᵁ W)
    (t : (secF 𝒪 W).obj (pushUnit V π)) : V.X.functionField :=
  V.X.presheaf.germ (π ⁻¹ᵁ W) (genericPoint V.X) hW (toΓY V π t)

omit [Surjective π] in
/-- `toFunctionField` commutes with restriction. -/
theorem toFunctionField_res [IsIntegral V.X] {W₁ W₂ : X.Opens} (hle : W₂ ≤ W₁)
    (h : genericPoint V.X ∈ π ⁻¹ᵁ W₂) (t : (secF 𝒪 W₁).obj (pushUnit V π)) :
    toFunctionField V π h ((secRestrict 𝒪 hle).app _ t) =
      toFunctionField V π (Scheme.Hom.preimage_mono π hle h) t := by
  unfold toFunctionField
  rw [toΓY_res]
  exact TopCat.Presheaf.germ_res_apply _ (homOfLE (Scheme.Hom.preimage_mono π hle)) _ h _

omit [Surjective π] in
/-- `toFunctionField` is additive. -/
theorem toFunctionField_sub [IsIntegral V.X] {W : X.Opens} (h : genericPoint V.X ∈ π ⁻¹ᵁ W)
    (t t' : (secF 𝒪 W).obj (pushUnit V π)) :
    toFunctionField V π h (t - t') = toFunctionField V π h t - toFunctionField V π h t' := by
  unfold toFunctionField
  rw [toΓY_sub, map_sub]

omit [Surjective π] in
/-- The rational function of a section over `W` is regular at every point over `W`. -/
theorem toFunctionField_mem_stalkSubring [IsIntegral V.X] {W : X.Opens}
    (h : genericPoint V.X ∈ π ⁻¹ᵁ W) {y : V.X} (hy : π y ∈ W)
    (t : (secF 𝒪 W).obj (pushUnit V π)) : toFunctionField V π h t ∈ stalkSubring y := by
  unfold toFunctionField
  have hy' : y ∈ π ⁻¹ᵁ W := hy
  refine ⟨V.X.presheaf.germ (π ⁻¹ᵁ W) y hy' (toΓY V π t), ?_⟩
  change V.X.presheaf.stalkSpecializes _ (V.X.presheaf.germ _ y hy' (toΓY V π t)) = _
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]

omit [Surjective π] in
/-- `toFunctionField` is injective. -/
theorem toFunctionField_injective [IsIntegral V.X] {W : X.Opens}
    (h : genericPoint V.X ∈ π ⁻¹ᵁ W) : Function.Injective (toFunctionField V π h) :=
  fun _ _ he => germ_injective_of_isIntegral (X := V.X) _ h he

/-- The generic point of an irreducible scheme lies over every open meeting the image of `f`. -/
theorem genericPoint_mem_preimage_of_mem {Y Z : Scheme.{u}} [IrreducibleSpace Y] (f : Y ⟶ Z)
    (W : Z.Opens) {y : Y} (hy : f y ∈ W) : genericPoint Y ∈ f ⁻¹ᵁ W :=
  ((genericPoint_spec Y).mem_open_set_iff (f ⁻¹ᵁ W).isOpen).mpr ⟨y, trivial, hy⟩

/-- A point of two opens lies in their intersection. -/
private theorem mem_inf_of_mem {X : Scheme.{u}} {W₁ W₂ : X.Opens} {x : X}
    (h₁ : x ∈ W₁) (h₂ : x ∈ W₂) : x ∈ W₁ ⊓ W₂ :=
  Opens.mem_inf.mpr ⟨h₁, h₂⟩

omit [Surjective π] in
/-- If `π⁻¹(W)` is the part of `Y` over the punctured spectrum, then `π` maps the generic point of
`Y` into `W`. -/
theorem map_genericPoint_mem_of_preimage_eq [IsIntegral V.X] {W : X.Opens}
    (hW : π ⁻¹ᵁ W = V.preimagePuncturedSpectrum) : π (genericPoint V.X) ∈ W := by
  change genericPoint V.X ∈ π ⁻¹ᵁ W
  rw [hW]
  exact genericPoint_mem_preimagePuncturedSpectrum V

omit [Surjective π] in
/-- **The polar lemma on `Y`.** If `s` is a cocycle of sections of `π_* 𝒪_Y` on a cover containing
`W` with `π⁻¹(W)` the part of `Y` over the punctured spectrum, then on each member `U a` of the
cover the rational function of `s a j₀` comes from a section over `U a`. -/
theorem exists_toFunctionField_eq_of_cocycle [IsNormal V.X] [IsIntegral V.X] {J : Type u}
    (U : J → X.Opens) (hU : ∀ x : X, ∃ j, x ∈ U j) (j₀ : J)
    (hj₀ : π ⁻¹ᵁ U j₀ = V.preimagePuncturedSpectrum)
    (s : ∀ a b, (secF 𝒪 (U a ⊓ U b)).obj (pushUnit V π))
    (hs : ∀ a b (ha : genericPoint V.X ∈ π ⁻¹ᵁ (U a ⊓ U j₀))
      (hb : genericPoint V.X ∈ π ⁻¹ᵁ (U b ⊓ U j₀)) (hab : genericPoint V.X ∈ π ⁻¹ᵁ (U a ⊓ U b)),
      toFunctionField V π ha (s a j₀) - toFunctionField V π hb (s b j₀) =
        toFunctionField V π hab (s a b))
    (a : J) :
    ∃ t : (secF 𝒪 (U a)).obj (pushUnit V π), ∀ (h₁ : genericPoint V.X ∈ π ⁻¹ᵁ U a)
      (h₂ : genericPoint V.X ∈ π ⁻¹ᵁ (U a ⊓ U j₀)),
      toFunctionField V π h₁ t = toFunctionField V π h₂ (s a j₀) := by
  set η := genericPoint V.X
  have hηW' : π η ∈ U j₀ := map_genericPoint_mem_of_preimage_eq V π hj₀
  choose j hj using hU
  have hηj : ∀ y : V.X, η ∈ π ⁻¹ᵁ (U (j (π y)) ⊓ U j₀) := fun y =>
    genericPoint_mem_preimage_of_mem π _
      (mem_inf_of_mem
        (show π η ∈ U (j (π y)) from genericPoint_mem_preimage_of_mem π _ (hj (π y))) hηW')
  let h : V.X → V.X.functionField := fun y => toFunctionField V π (hηj y) (s (j (π y)) j₀)
  have hA : ∀ y : V.X, Order.coheight y = 1 → V.f y ≠ IsLocalRing.closedPoint V.A →
      h y ∈ stalkSubring y := by
    intro y _ hy
    exact toFunctionField_mem_stalkSubring V π _
      (mem_inf_of_mem (hj (π y)) (show y ∈ π ⁻¹ᵁ U j₀ by rwa [hj₀])) _
  have hB : ∀ y : V.X, ∃ W' : V.X.Opens, y ∈ W' ∧ ∀ y' ∈ W', h y - h y' ∈ stalkSubring y' := by
    intro y
    refine ⟨π ⁻¹ᵁ U (j (π y)), hj (π y), fun y' hy' => ?_⟩
    have hab : η ∈ π ⁻¹ᵁ (U (j (π y)) ⊓ U (j (π y'))) := genericPoint_mem_preimage_of_mem π _
      (mem_inf_of_mem hy' (hj (π y')))
    change toFunctionField V π _ _ - toFunctionField V π _ _ ∈ _
    rw [hs (j (π y)) (j (π y')) (hηj y) (hηj y') hab]
    exact toFunctionField_mem_stalkSubring V π hab (mem_inf_of_mem hy' (hj (π y'))) _
  have hpolar := forall_mem_stalkSubring_of_polar_of_isModification V.dimension_two V.f
    V.modification h hA hB
  by_cases hne : η ∈ π ⁻¹ᵁ U a
  · have : Nonempty (π ⁻¹ᵁ U a) := ⟨⟨η, hne⟩⟩
    have hne₂ : η ∈ π ⁻¹ᵁ (U a ⊓ U j₀) := mem_inf_of_mem hne hηW'
    obtain ⟨t, ht⟩ := exists_germToFunctionField_eq_of_forall_mem_range V.X (π ⁻¹ᵁ U a)
      (toFunctionField V π hne₂ (s a j₀)) (fun y => by
        have hy : π y.1 ∈ U a := y.2
        have hab : η ∈ π ⁻¹ᵁ (U (j (π y.1)) ⊓ U a) := genericPoint_mem_preimage_of_mem π _
          (mem_inf_of_mem (hj (π y.1)) hy)
        have hx : toFunctionField V π hne₂ (s a j₀) =
            h y.1 - toFunctionField V π hab (s (j (π y.1)) a) := by
          rw [← hs (j (π y.1)) a (hηj y.1) hne₂ hab]
          abel
        rw [hx]
        exact sub_mem (hpolar y.1)
          (toFunctionField_mem_stalkSubring V π _ (mem_inf_of_mem (hj (π y.1)) hy) _))
    exact ⟨t, fun _ _ => ht⟩
  · exact ⟨0, fun h₁ => absurd h₁ hne⟩

omit [Surjective π] in
/-- A cocycle `s` of sections of `π_* 𝒪_Y` on a cover containing `W`, with `π⁻¹(W)` the part of
`Y` over the punctured spectrum, is a Čech coboundary on every overlap over which the generic point
of `Y` lies. -/
theorem exists_eq_sub_of_toFunctionField_cocycle [IsNormal V.X] [IsIntegral V.X] {J : Type u}
    (U : J → X.Opens) (hU : ∀ x : X, ∃ j, x ∈ U j) (j₀ : J)
    (hj₀ : π ⁻¹ᵁ U j₀ = V.preimagePuncturedSpectrum)
    (s : ∀ a b, (secF 𝒪 (U a ⊓ U b)).obj (pushUnit V π))
    (hs : ∀ a b (ha : genericPoint V.X ∈ π ⁻¹ᵁ (U a ⊓ U j₀))
      (hb : genericPoint V.X ∈ π ⁻¹ᵁ (U b ⊓ U j₀)) (hab : genericPoint V.X ∈ π ⁻¹ᵁ (U a ⊓ U b)),
      toFunctionField V π ha (s a j₀) - toFunctionField V π hb (s b j₀) =
        toFunctionField V π hab (s a b)) :
    ∃ t : ∀ a, (secF 𝒪 (U a)).obj (pushUnit V π), ∀ a b,
      genericPoint V.X ∈ π ⁻¹ᵁ (U a ⊓ U b) →
        s a b = (secRestrict 𝒪 inf_le_left).app _ (t a) -
          (secRestrict 𝒪 inf_le_right).app _ (t b) := by
  have hηW' := map_genericPoint_mem_of_preimage_eq V π hj₀
  choose t ht using exists_toFunctionField_eq_of_cocycle V π U hU j₀ hj₀ s hs
  refine ⟨t, fun a b hab => toFunctionField_injective V π hab ?_⟩
  obtain ⟨ha, hb⟩ : π (genericPoint V.X) ∈ U a ∧ π (genericPoint V.X) ∈ U b :=
    Opens.mem_inf.mp hab
  rw [toFunctionField_sub, toFunctionField_res, toFunctionField_res,
    ht a ha (mem_inf_of_mem ha hηW'),
    ht b hb (mem_inf_of_mem hb hηW'), hs a b (mem_inf_of_mem ha hηW') (mem_inf_of_mem hb hηW') hab]

/-- **Local primitives glue, for the direct image of `𝒪_Y`.** -/
theorem exists_d_eq_of_local_primitives_pushforward [IsNormal V.X] [IsIntegral V.X]
    (I : InjectiveResolution (pushUnit V π)) (W : X.Opens)
    (hW : π ⁻¹ᵁ W = V.preimagePuncturedSpectrum)
    {J : Type u} (U : J → X.Opens) (hU : ∀ x : X, ∃ j, x ∈ U j) (j₀ : J)
    (hj₀ : U j₀ = W)
    (c : (secF 𝒪 ⊤).obj (I.cocomplex.X 1))
    (e : ∀ j, (secF 𝒪 (U j)).obj (I.cocomplex.X 0))
    (he : ∀ j, (secF 𝒪 (U j)).map (I.cocomplex.d 0 1) (e j) =
      (secRestrict 𝒪 (le_top : U j ≤ ⊤)).app _ c) :
    ∃ ε : (secF 𝒪 ⊤).obj (I.cocomplex.X 0), (secF 𝒪 ⊤).map (I.cocomplex.d 0 1) ε = c := by
  have hexact := fun W : X.Opens => exact_mono_secF_ι₀ I W
  have hs : ∀ a b, ∃ t : (secF 𝒪 (U a ⊓ U b)).obj (pushUnit V π),
      (secF 𝒪 _).map (ι₀ I) t = (secRestrict 𝒪 inf_le_left).app _ (e a) -
        (secRestrict 𝒪 inf_le_right).app _ (e b) := by
    intro a b
    refine (ShortComplex.ab_exact_iff _).mp (hexact (U a ⊓ U b)).1 _ ?_
    change (secF 𝒪 _).map (I.cocomplex.d 0 1) (_ - _) = 0
    rw [map_sub, ← secRestrict_app_map, ← secRestrict_app_map, he, he, secRestrict_app_comp,
      secRestrict_app_comp, sub_self]
  choose s hs using hs
  have hkey : ∀ a b, (secRestrict 𝒪 (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        U a ⊓ U b ⊓ U j₀ ≤ U a ⊓ U j₀)).app _ (s a j₀) -
      (secRestrict 𝒪 (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        U a ⊓ U b ⊓ U j₀ ≤ U b ⊓ U j₀)).app _ (s b j₀) =
      (secRestrict 𝒪 (inf_le_left : U a ⊓ U b ⊓ U j₀ ≤ U a ⊓ U b)).app _ (s a b) := by
    intro a b
    apply (AddCommGrpCat.mono_iff_injective _).mp (hexact _).2
    rw [map_sub, ← secRestrict_app_map, ← secRestrict_app_map, ← secRestrict_app_map, hs, hs,
      hs, map_sub, map_sub, map_sub, secRestrict_app_comp, secRestrict_app_comp,
      secRestrict_app_comp, secRestrict_app_comp, secRestrict_app_comp, secRestrict_app_comp]
    abel
  obtain ⟨t, ht⟩ := exists_eq_sub_of_toFunctionField_cocycle V π U hU j₀ (by rw [hj₀, hW]) s
    fun a b ha hb hab => by
      have h₃ : genericPoint V.X ∈ π ⁻¹ᵁ (U a ⊓ U b ⊓ U j₀) :=
        Opens.mem_inf.mpr ⟨hab, (Opens.mem_inf.mp ha).2⟩
      have := congrArg (toFunctionField V π h₃) (hkey a b)
      rwa [toFunctionField_sub, toFunctionField_res, toFunctionField_res,
        toFunctionField_res] at this
  refine exists_d_eq_of_cech I U (fun _ => le_top) (fun x _ => Opens.mem_iSup.mpr (hU x)) c e he
    t fun a b => ?_
  by_cases hab : genericPoint V.X ∈ π ⁻¹ᵁ (U a ⊓ U b)
  · rw [← ht a b hab]
    exact hs a b
  · refine eq_of_isEmpty' (G := (SheafOfModules.toSheaf 𝒪).obj (I.cocomplex.X 0))
      (fun x hx => hab ?_) _ _
    obtain ⟨y, rfl⟩ := π.surjective x
    exact genericPoint_mem_preimage_of_mem π _ hx

end Pushforward

end AlgebraicGeometry.PuncturedRestriction

end
