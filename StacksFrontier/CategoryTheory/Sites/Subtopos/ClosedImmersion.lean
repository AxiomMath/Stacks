module

public import StacksFrontier.CategoryTheory.Sites.CartesianClosed
public import StacksFrontier.CategoryTheory.Sites.Subtopos.Immersions

/-!
# Closed immersions of topoi

Stacks 08M1 lists seven properties of the pushforward of a closed immersion of topoi. Four of
them — fully faithfulness and the reflection of injections, surjections and bijections — hold
for any embedding. The remaining three say that `i_*` commutes with coequalizers and pushouts
and takes surjections to surjections; they hold because the essential image of `i_*` is a
closed complement `closedComplement F`, and such a subcategory is stable under the *connected*
colimits computed in `Sh(C)`: multiplying by `F` preserves colimits (the sheaf topos is
cartesian closed) and turns the diagram into one whose transition maps are isomorphisms.

Everything here is stated for sheaves of sets valued in `Type (max u v)`, the canonical size
for a site `C : Type u` with `Category.{v} C`, because that is the size at which the sheaf
topos is known to be cartesian closed
(`CategoryTheory.Sheaf.monoidalClosed_sheaf_type`); the source site of the immersion is taken
in the same universes, as in `IsSubtopos`.

## Main results

* `MorphismOfTopoi.IsClosedImmersion.fullyFaithful`,
  `MorphismOfTopoi.IsClosedImmersion.preservesColimitsOfShape_walkingParallelPair`,
  `MorphismOfTopoi.IsClosedImmersion.preservesColimitsOfShape_walkingSpan`,
  `MorphismOfTopoi.IsClosedImmersion.preservesEpimorphisms`,
  `MorphismOfTopoi.IsClosedImmersion.reflectsMonomorphisms`,
  `MorphismOfTopoi.IsClosedImmersion.reflectsEpimorphisms`,
  `MorphismOfTopoi.IsClosedImmersion.reflectsIsomorphisms`: the seven clauses of Stacks 08M1.

Tags covered: 08M1.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

section Auxiliary

variable {A : Type u} [Category.{v} A]

/-- A faithful functor reflects epimorphisms. -/
lemma reflectsEpimorphisms_of_faithful {B : Type*} [Category* B] (T : A ⥤ B) [T.Faithful] :
    T.ReflectsEpimorphisms where
  reflects f hf := ⟨fun a b hab => T.map_injective ((cancel_epi (T.map f)).1 (by
    rw [← T.map_comp, ← T.map_comp, hab]))⟩

/-- The projection of a colimit cofork over a pair of *equal* morphisms is an isomorphism. -/
lemma isIso_cofork_π_of_eq {X Y : A} {f g : X ⟶ Y} (hfg : f = g) {c : Cofork f g}
    (hc : IsColimit c) : IsIso c.π := by
  have hs : f ≫ 𝟙 Y = g ≫ 𝟙 Y := by rw [hfg]
  have h1 : c.π ≫ hc.desc (Cofork.ofπ (𝟙 Y) hs) = 𝟙 Y := by simp
  have h2 : hc.desc (Cofork.ofπ (𝟙 Y) hs) ≫ c.π = 𝟙 c.pt :=
    Cofork.IsColimit.hom_ext hc (by
      rw [← Category.assoc, h1, Category.id_comp, Category.comp_id])
  exact ⟨⟨_, h1, h2⟩⟩

/-- In a pushout square whose left-hand leg is an isomorphism, the opposite leg is an
isomorphism. -/
lemma isIso_inr_of_isPushout {X Y Z P : A} {f : X ⟶ Y} {g : X ⟶ Z} {inl : Y ⟶ P} {inr : Z ⟶ P}
    (s : IsPushout f g inl inr) (hf : IsIso f) : IsIso inr := by
  have hw : f ≫ (inv f ≫ g) = g ≫ 𝟙 Z := by simp
  refine ⟨⟨s.desc (inv f ≫ g) (𝟙 Z) hw, s.inr_desc _ _ hw, s.hom_ext ?_ ?_⟩⟩
  · rw [s.inl_desc_assoc, Category.assoc, ← s.w, IsIso.inv_hom_id_assoc, Category.comp_id]
  · rw [s.inr_desc_assoc, Category.id_comp, Category.comp_id]

variable [HasBinaryProducts A] {F G G' : A}

/-- The first projection is natural in the second factor: applying `F ⨯ -` to `g : G ⟶ G'`
and then projecting to `F` gives back the projection to `F`. -/
lemma prodFunctorObj_map_comp_fst (g : G ⟶ G') :
    (prod.functor.obj F).map g ≫ prod.fst = (prod.fst : F ⨯ G ⟶ F) := by
  change prod.map (𝟙 F) g ≫ prod.fst = _
  rw [prod.map_fst, Category.comp_id]

/-- If both projections `F ⨯ G ⟶ F` and `F ⨯ G' ⟶ F` are isomorphisms, then so is `F ⨯ g`
for every `g : G ⟶ G'`. -/
lemma isIso_prodFunctorObj_map (g : G ⟶ G') (hG : IsIso (prod.fst : F ⨯ G ⟶ F))
    (hG' : IsIso (prod.fst : F ⨯ G' ⟶ F)) : IsIso ((prod.functor.obj F).map g) :=
  @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ hG' hG (prodFunctorObj_map_comp_fst g)

/-- If `F ⨯ g` and the projection `F ⨯ G ⟶ F` are isomorphisms, then so is the projection
`F ⨯ G' ⟶ F`. -/
lemma isIso_fst_of_isIso_prodFunctorObj_map (g : G ⟶ G')
    (hg : IsIso ((prod.functor.obj F).map g)) (hG : IsIso (prod.fst : F ⨯ G ⟶ F)) :
    IsIso (prod.fst : F ⨯ G' ⟶ F) :=
  @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ hg hG (prodFunctorObj_map_comp_fst g)

end Auxiliary

/-! ## The closed complement is stable under connected colimits -/

section ClosedComplement

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (F : Sheaf J (Type (max u v)))

/-- Multiplication by a fixed sheaf preserves all colimits: the topos of sheaves of sets on a
site is cartesian closed (`CategoryTheory.Sheaf.monoidalClosed_sheaf_type`), so `F ⨯ -` is
naturally isomorphic to a left adjoint. -/
lemma preservesColimitsOfShape_prodFunctorObj (K : Type w) [Category.{w} K] :
    PreservesColimitsOfShape K (prod.functor.obj F) := by
  let _ : MonoidalClosed (Sheaf J (Type (max u v))) := Sheaf.monoidalClosed_sheaf_type J
  have hpc : PreservesColimitsOfShape K (tensorLeft F) := inferInstance
  exact @preservesColimitsOfShape_of_natIso _ _ _ _ K _ _ _
    (CartesianMonoidalCategory.tensorLeftIsoProd F) hpc

/-- The closed complement of `F` — the sheaves `G` for which `prod.fst : F ⨯ G ⟶ F` is an
isomorphism — is closed under isomorphism, because `F ⨯ e` is an isomorphism whenever `e` is. -/
instance : (closedComplement F).IsClosedUnderIsomorphisms where
  of_iso e hG :=
    isIso_fst_of_isIso_prodFunctorObj_map e.hom
      (inferInstanceAs (IsIso ((prod.functor.obj F).map e.hom))) hG

/-- The closed complement of `F` is stable under coequalizers: multiplying a parallel pair by `F`
makes its two maps equal, so the coequalizer projection becomes an isomorphism and the colimit
inherits the defining isomorphism from `T.obj one`. -/
instance : (closedComplement F).IsClosedUnderColimitsOfShape WalkingParallelPair := by
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨T, hT⟩
  have := preservesColimitsOfShape_prodFunctorObj F WalkingParallelPair
  have h1 : IsIso (prod.fst : F ⨯ T.obj WalkingParallelPair.one ⟶ F) := hT _
  have hab : (prod.functor.obj F).map (T.map WalkingParallelPairHom.left) =
      (prod.functor.obj F).map (T.map WalkingParallelPairHom.right) :=
    (cancel_mono (prod.fst : F ⨯ T.obj WalkingParallelPair.one ⟶ F)).1
      ((prodFunctorObj_map_comp_fst _).trans (prodFunctorObj_map_comp_fst _).symm)
  have hπ : IsIso ((prod.functor.obj F).map (coequalizer.π
      (T.map WalkingParallelPairHom.left) (T.map WalkingParallelPairHom.right))) :=
    isIso_cofork_π_of_eq hab
      (isColimitOfHasCoequalizerOfPreservesColimit (prod.functor.obj F) _ _)
  exact ObjectProperty.prop_of_iso _
    (HasColimit.isoOfNatIso (diagramIsoParallelPair T)).symm
    (isIso_fst_of_isIso_prodFunctorObj_map _ hπ h1)

/-- The closed complement of `F` is stable under pushouts: multiplying a span by `F` makes the
left-hand leg an isomorphism, hence also the opposite leg `pushout.inr`, so the pushout inherits
the defining isomorphism from `T.obj right`. -/
instance : (closedComplement F).IsClosedUnderColimitsOfShape WalkingSpan := by
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨T, hT⟩
  have := preservesColimitsOfShape_prodFunctorObj F WalkingSpan
  have h0 : IsIso (prod.fst : F ⨯ T.obj WalkingSpan.zero ⟶ F) := hT _
  have hl : IsIso (prod.fst : F ⨯ T.obj WalkingSpan.left ⟶ F) := hT _
  have hr : IsIso (prod.fst : F ⨯ T.obj WalkingSpan.right ⟶ F) := hT _
  have hΦa : IsIso ((prod.functor.obj F).map (T.map WalkingSpan.Hom.fst)) :=
    isIso_prodFunctorObj_map _ h0 hl
  have hinr : IsIso ((prod.functor.obj F).map
      (pushout.inr (T.map WalkingSpan.Hom.fst) (T.map WalkingSpan.Hom.snd))) :=
    isIso_inr_of_isPushout
      ((IsPushout.of_hasPushout _ _).map (prod.functor.obj F)) hΦa
  exact ObjectProperty.prop_of_iso _
    (HasColimit.isoOfNatIso (diagramIsoSpan T)).symm
    (isIso_fst_of_isIso_prodFunctorObj_map _ hinr hr)

end ClosedComplement

/-! ## Closed immersions -/

namespace MorphismOfTopoi

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
  {i : MorphismOfTopoi (Sheaf K (Type (max u v))) (Sheaf J (Type (max u v)))}

namespace IsClosedImmersion

/-- The pushforward of a closed immersion of topoi is fully faithful. This is the first
assertion of Stacks 08M1; it already holds for an embedding. -/
@[stacks 08M1]
noncomputable def fullyFaithful (hi : i.IsClosedImmersion) : i.pushforward.FullyFaithful :=
  hi.1.fullyFaithful

/-- The pushforward of a closed immersion of topoi preserves colimits of every shape under
which the closed complement is stable: the essential image of `i_*` is such a complement, so
those colimits are computed in `Sh(C)`. -/
private lemma preservesColimitsOfShape_aux (hi : i.IsClosedImmersion) (K' : Type w)
    [Category.{w} K'] [HasColimitsOfShape K' (Sheaf J (Type (max u v)))]
    (hcl : ∀ F : Sheaf J (Type (max u v)),
      (closedComplement F).IsClosedUnderColimitsOfShape K') :
    PreservesColimitsOfShape K' i.pushforward := by
  obtain ⟨hemb, F, -, hPF⟩ := hi
  have hfull : i.pushforward.Full := hemb.full
  have hfaithful : i.pushforward.Faithful := hemb.faithful
  have : (i.pushforward.essImage).IsClosedUnderColimitsOfShape K' := hPF ▸ hcl F
  have : i.pushforward.toEssImage.IsEquivalence := { }
  have : PreservesColimitsOfShape K' (i.pushforward.toEssImage ⋙ i.pushforward.essImage.ι) :=
    inferInstance
  exact preservesColimitsOfShape_of_natIso i.pushforward.toEssImageCompι

/-- **Stacks Project, Lemma 7.43.8 (tag 08M1).** The pushforward of a closed immersion of
topoi commutes with coequalizers. -/
@[stacks 08M1]
lemma preservesColimitsOfShape_walkingParallelPair (hi : i.IsClosedImmersion) :
    PreservesColimitsOfShape WalkingParallelPair i.pushforward :=
  preservesColimitsOfShape_aux hi _ fun _ => inferInstance

/-- **Stacks Project, Lemma 7.43.8 (tag 08M1).** The pushforward of a closed immersion of
topoi commutes with pushouts. -/
@[stacks 08M1]
lemma preservesColimitsOfShape_walkingSpan (hi : i.IsClosedImmersion) :
    PreservesColimitsOfShape WalkingSpan i.pushforward :=
  preservesColimitsOfShape_aux hi _ fun _ => inferInstance

/-- **Stacks Project, Lemma 7.43.8 (tag 08M1).** The pushforward of a closed immersion of
topoi transforms surjections into surjections. -/
@[stacks 08M1]
lemma preservesEpimorphisms (hi : i.IsClosedImmersion) :
    i.pushforward.PreservesEpimorphisms where
  preserves f _ :=
    have : PreservesColimitsOfShape WalkingSpan i.pushforward :=
      preservesColimitsOfShape_walkingSpan hi
    preserves_epi_of_preservesColimit i.pushforward f

/-- **Stacks Project, Lemma 7.43.8 (tag 08M1).** The pushforward of a closed immersion of
topoi reflects injections. -/
@[stacks 08M1]
lemma reflectsMonomorphisms (hi : i.IsClosedImmersion) :
    i.pushforward.ReflectsMonomorphisms :=
  have : i.pushforward.Faithful := hi.1.faithful
  Functor.reflectsMonomorphisms_of_faithful _

/-- **Stacks Project, Lemma 7.43.8 (tag 08M1).** The pushforward of a closed immersion of
topoi reflects surjections. -/
@[stacks 08M1]
lemma reflectsEpimorphisms (hi : i.IsClosedImmersion) :
    i.pushforward.ReflectsEpimorphisms :=
  have : i.pushforward.Faithful := hi.1.faithful
  reflectsEpimorphisms_of_faithful _

/-- **Stacks Project, Lemma 7.43.8 (tag 08M1).** The pushforward of a closed immersion of
topoi reflects bijections. -/
@[stacks 08M1]
lemma reflectsIsomorphisms (hi : i.IsClosedImmersion) :
    i.pushforward.ReflectsIsomorphisms :=
  have : i.pushforward.Full := hi.1.full
  have : i.pushforward.Faithful := hi.1.faithful
  inferInstance

end IsClosedImmersion

end MorphismOfTopoi
