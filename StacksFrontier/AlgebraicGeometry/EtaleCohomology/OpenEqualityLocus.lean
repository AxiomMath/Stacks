module

public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.ZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubterminalSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.LeftKanExtensionExactness
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Comparison

/-!
# The open locus where two sections of an étale sheaf agree

Let `S` be a scheme in a big étale site `B` and let `F` be a sheaf of sets on the small étale
site of `S`. Two global sections of `F` agree on a largest open subscheme of `S`: there is an
open `W ⊆ S` such that a morphism `f : T ⟶ S` of the big étale site factors through `W` exactly
when the two sections become equal after inverse image along the induced morphism of small étale
topoi.

The open is produced by the subterminal-sheaf correspondence. The equalizer of the two sections,
taken in the category of sheaves, is a subsheaf of the final sheaf, so by Stacks 04HV it is
represented by a unique open `W`. Inverse image along `f` preserves finite limits, so it carries
that equalizer to the equalizer of the two restricted sections; the restricted sections are equal
exactly when their equalizer is the final sheaf, which happens exactly when the base change of
`W` along `f` is the final object of the small étale site of `T`, that is, when `f` factors
through `W`.

## Main definitions

* `AlgebraicGeometry.openEqLocus` — the largest open of `S` on which the two sections agree.

## Main results

* `AlgebraicGeometry.factorsThrough_openEqLocus_iff` — the universal property characterising the
  morphisms that factor through that open.

## Implementation notes

The two sections are given as morphisms out of the terminal sheaf rather than as elements of
`F(S)`; this is the same datum and it makes the equalizer available without choosing an
identification of the base change of the terminal sheaf with the terminal sheaf.

`AlgebraicGeometry.openEqLocus` is defined as the supremum of the opens through which only
agreeing morphisms factor, so that it involves no choice; it is identified with the open
furnished by Stacks 04HV in `AlgebraicGeometry.openEqLocus_eq_equalizerOpen`.

## References

* [Stacks Project, Tag 09XM](https://stacks.math.columbia.edu/tag/09XM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-! ### The equalizer of two global sections is represented by an open -/

/-- The equalizer of two morphisms out of the terminal object is a subobject of the terminal
object. -/
private theorem equalizer_isSubterminal {C : Type*} [Category C] [HasTerminal C]
    [HasEqualizers C] {F : C} (s t : ⊤_ C ⟶ F) : IsSubterminal (equalizer s t) :=
  IsSubterminal.def.2 fun _ _ _ => (cancel_mono (equalizer.ι s t)).1 (terminal.hom_ext _ _)

variable (B : BigEtaleSite.{u})

/-- The equalizer of two global sections of a sheaf on the small étale site is represented by an
open subscheme of the base. -/
private theorem exists_open_representation_equalizer (S : B.Scheme)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (max (u + 1) v)))
    (s t : terminal (Sheaf (SmallEtale.topology B S.obj S.property)
      (Type (max (u + 1) v))) ⟶ F) :
    ∃ W : (B.inclusion.obj S).Opens,
      Nonempty ((equalizer s t) ≅
        (presheafToSheaf (SmallEtale.topology B S.obj S.property)
          (Type (max (u + 1) v))).obj (openRepresentable.{u, v} B S.obj S.property W)) :=
  ⟨_, (existsUnique_open_of_isSubterminal B S.obj S.property (equalizer s t)
    (equalizer_isSubterminal s t)).choose_spec.1⟩

/-- The open subscheme of `S` representing the equalizer of two global sections. -/
private def equalizerOpen (S : B.Scheme)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (max (u + 1) v)))
    (s t : terminal (Sheaf (SmallEtale.topology B S.obj S.property)
      (Type (max (u + 1) v))) ⟶ F) : (B.inclusion.obj S).Opens :=
  Classical.choose (exists_open_representation_equalizer.{u, v} B S F s t)

/-- The equalizer of two global sections is the sheaf represented by `equalizerOpen`. -/
private theorem equalizerOpen_representation (S : B.Scheme)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (max (u + 1) v)))
    (s t : terminal (Sheaf (SmallEtale.topology B S.obj S.property)
      (Type (max (u + 1) v))) ⟶ F) :
    Nonempty ((equalizer s t) ≅
      (presheafToSheaf (SmallEtale.topology B S.obj S.property)
        (Type (max (u + 1) v))).obj
        (openRepresentable.{u, v} B S.obj S.property (equalizerOpen.{u, v} B S F s t))) :=
  Classical.choose_spec (exists_open_representation_equalizer.{u, v} B S F s t)

/-! ### Representable sheaves on the small étale site -/

/-- The canonical functor from the small étale site of `S` to the schemes over `S`. -/
private abbrev toOver (S : B.Scheme) :
    SmallEtale B S.obj S.property ⥤ Over (B.inclusion.obj S) :=
  SmallEtale.inclusion B S.obj S.property ⋙ Over.post (X := S) B.inclusion

/-- The canonical functor from the small étale site of `S` to the schemes over `S` is fully
faithful. -/
private def toOverFullyFaithful (S : B.Scheme) : (toOver B S).FullyFaithful := by
  letI : B.inclusion.Full := ObjectProperty.full_ι _
  letI : B.inclusion.Faithful := ObjectProperty.faithful_ι _
  letI : (SmallEtale.inclusion B S.obj S.property).Full := ObjectProperty.full_ι _
  letI : (SmallEtale.inclusion B S.obj S.property).Faithful := ObjectProperty.faithful_ι _
  haveI : (Over.post (X := S) B.inclusion).Full := inferInstance
  haveI : (Over.post (X := S) B.inclusion).Faithful := inferInstance
  haveI : (toOver B S).Full := Functor.Full.comp _ _
  haveI : (toOver B S).Faithful := Functor.Faithful.comp _ _
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- The presheaf on the small étale site represented by an object of that site, as the
restriction of the presheaf it represents on the schemes over `S`.

The comparison is full faithfulness of the canonical functor to the schemes over `S`. -/
private def representablePresheafIso (S : B.Scheme) (A : SmallEtale B S.obj S.property) :
    (toOver B S).op ⋙ uliftYoneda.{max (u + 1) v}.obj ((toOver B S).obj A) ≅
      (uliftYoneda.{max (u + 1) v} (C := SmallEtale B S.obj S.property)).obj A := by
  let FF := toOverFullyFaithful B S
  refine NatIso.ofComponents (fun X => Equiv.toIso (Equiv.ulift.trans
    ((FF.homEquiv (X := X.unop) (Y := A)).symm.trans Equiv.ulift.symm))) ?_
  intro X Y f
  ext ⟨x⟩
  change (toOver B S).obj X.unop ⟶ (toOver B S).obj A at x
  apply ULift.ext
  change FF.preimage ((toOver B S).map f.unop ≫ x) = f.unop ≫ FF.preimage x
  apply FF.homEquiv.injective
  change (toOver B S).map (FF.preimage ((toOver B S).map f.unop ≫ x)) =
    (toOver B S).map (f.unop ≫ FF.preimage x)
  rw [FF.map_preimage, Functor.map_comp, FF.map_preimage]

/-- The presheaf on the small étale site represented by an object of that site is a sheaf.

The fpqc topology on the schemes over `S` is subcanonical, so the presheaf represented upstairs
is an fpqc sheaf, and an fpqc sheaf restricts to a sheaf on the chosen small étale site. -/
private theorem representablePresheaf_isSheaf (S : B.Scheme)
    (A : SmallEtale B S.obj S.property) :
    Presheaf.IsSheaf (SmallEtale.topology B S.obj S.property)
      ((uliftYoneda.{max (u + 1) v} (C := SmallEtale B S.obj S.property)).obj A) := by
  have hF : Presheaf.IsSheaf (Scheme.fpqcTopology.over (B.inclusion.obj S))
      ((uliftYoneda.{max (u + 1) v} (C := Over (B.inclusion.obj S))).obj
        ((toOver B S).obj A)) := by
    rw [isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  exact (Presheaf.isSheaf_of_iso_iff (representablePresheafIso.{u, v} B S A)).mp
    (isSheaf_chosenSmallEtale_of_isSheaf_fpqc B S.obj S.property _ hF)

/-- The presheaf represented by an open subscheme of `S` is the presheaf represented by that
open viewed as an object of the small étale site. -/
private def openRepresentableIso (S : B.Scheme) (W : (B.inclusion.obj S).Opens) :
    openRepresentable.{u, v} B S.obj S.property W ≅
      (uliftYoneda.{max (u + 1) v} (C := SmallEtale B S.obj S.property)).obj
        ((opensToBoundedEtale B S.obj S.property).obj W) :=
  representablePresheafIso.{u, v} B S ((opensToBoundedEtale B S.obj S.property).obj W)

/-- Sheafifying the presheaf represented by an open subscheme gives the sheafification of the
presheaf represented by that open as an object of the small étale site. -/
private def openSheafificationIso (S : B.Scheme) (W : (B.inclusion.obj S).Opens) :
    (presheafToSheaf (SmallEtale.topology B S.obj S.property)
        (Type (max (u + 1) v))).obj (openRepresentable.{u, v} B S.obj S.property W) ≅
      (presheafToSheaf (SmallEtale.topology B S.obj S.property)
        (Type (max (u + 1) v))).obj
        ((uliftYoneda.{max (u + 1) v} (C := SmallEtale B S.obj S.property)).obj
          ((opensToBoundedEtale B S.obj S.property).obj W)) :=
  (presheafToSheaf (SmallEtale.topology B S.obj S.property)
    (Type (max (u + 1) v))).mapIso (openRepresentableIso.{u, v} B S W)

/-- The sheafification of the presheaf represented by an object of the small étale site is the
final sheaf exactly when that object is the final object of the site.

Sheafification is left adjoint to the inclusion of sheaves and the represented presheaf is
already a sheaf, so morphisms out of the sheafification are morphisms in the site. -/
private theorem representableSheafification_isTerminal_iff (S : B.Scheme)
    (A : SmallEtale B S.obj S.property) :
    Nonempty (IsTerminal ((presheafToSheaf (SmallEtale.topology B S.obj S.property)
        (Type (max (u + 1) v))).obj
      ((uliftYoneda.{max (u + 1) v} (C := SmallEtale B S.obj S.property)).obj A))) ↔
      Nonempty (IsTerminal A) := by
  let J := SmallEtale.topology B S.obj S.property
  let C := SmallEtale B S.obj S.property
  let a := presheafToSheaf J (Type (max (u + 1) v))
  let Qsh : Sheaf J (Type (max (u + 1) v)) :=
    ⟨(uliftYoneda.{max (u + 1) v} (C := C)).obj A, representablePresheaf_isSheaf.{u, v} B S A⟩
  let ec : a.obj ((uliftYoneda.{max (u + 1) v} (C := C)).obj A) ≅ Qsh :=
    asIso ((sheafificationAdjunction J (Type (max (u + 1) v))).counit.app Qsh)
  refine ⟨fun ⟨h⟩ => ?_, fun ⟨hA⟩ => ⟨IsTerminal.isTerminalObj a _
    (IsTerminal.isTerminalObj (uliftYoneda.{max (u + 1) v} (C := C)) _ hA)⟩⟩
  have hQterm : IsTerminal Qsh := h.ofIso ec
  have : ∀ X : C, Unique (X ⟶ A) := fun X => by
    let e : (a.obj ((uliftYoneda.{max (u + 1) v} (C := C)).obj X) ⟶ Qsh) ≃ ULift (X ⟶ A) :=
      ((sheafificationAdjunction J (Type (max (u + 1) v))).homEquiv _ _).trans
        (uliftYonedaEquiv.{max (u + 1) v} (X := X) (F := Qsh.obj))
    let m := hQterm.from (a.obj ((uliftYoneda.{max (u + 1) v} (C := C)).obj X))
    refine ⟨⟨(e m).down⟩, fun f => ?_⟩
    exact congrArg ULift.down (show ULift.up f = e m by
      simpa using congrArg e (hQterm.hom_ext (e.symm (ULift.up f)) m))
  exact ⟨IsTerminal.ofUnique A⟩

/-! ### Inverse image of a representable sheaf -/

/-- Inverse image along a continuous functor carries the sheaf represented by an object to the
sheaf represented by its image.

Both sides corepresent the same functor on sheaves: morphisms out of the inverse image are, by
the adjunction, morphisms into the direct image, which are sections of the target over the
image object. -/
private def sheafPullbackUliftYonedaIso {C D : Type (u + 1)} [Category.{u, u + 1} C]
    [Category.{u, u + 1} D] (G : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [G.IsContinuous J K]
    [HasWeakSheafify J (Type (max (u + 1) v))] [HasWeakSheafify K (Type (max (u + 1) v))]
    (A : C) :
    (G.sheafPullback (Type (max (u + 1) v)) J K).obj
        ((presheafToSheaf J (Type (max (u + 1) v))).obj
          ((uliftYoneda.{max (u + 1) v} (C := C)).obj A)) ≅
      (presheafToSheaf K (Type (max (u + 1) v))).obj
        ((uliftYoneda.{max (u + 1) v} (C := D)).obj (G.obj A)) := by
  let E := Type (max (u + 1) v)
  let P := (G.sheafPullback E J K).obj
    ((presheafToSheaf J E).obj ((uliftYoneda.{max (u + 1) v} (C := C)).obj A))
  let Q := (presheafToSheaf K E).obj ((uliftYoneda.{max (u + 1) v} (C := D)).obj (G.obj A))
  let rhsEquiv (H : Sheaf K E) : (Q ⟶ H) ≃ H.obj.obj (Opposite.op (G.obj A)) :=
    ((sheafificationAdjunction K E).homEquiv _ _).trans
      (uliftYonedaEquiv.{max (u + 1) v} (C := D) (X := G.obj A))
  let lhsEquiv' (H : Sheaf K E) :
      (P ⟶ H) ≃ ((sheafToPresheaf J E).obj
        ((G.sheafPushforwardContinuous E J K).obj H)).obj (Opposite.op A) :=
    ((G.sheafAdjunctionContinuous E J K).homEquiv _ _).trans
      (((sheafificationAdjunction J E).homEquiv _ _).trans
        (uliftYonedaEquiv.{max (u + 1) v} (C := C) (X := A)))
  let lhsEquiv (H : Sheaf K E) : (P ⟶ H) ≃ H.obj.obj (Opposite.op (G.obj A)) := by
    simpa [Functor.sheafPushforwardContinuous] using lhsEquiv' H
  have lhsNaturality (H H' : Sheaf K E) (α : H ⟶ H') (g : P ⟶ H) :
      lhsEquiv H' (g ≫ α) = (α.hom.app (Opposite.op (G.obj A))) (lhsEquiv H g) := by
    change lhsEquiv' H' (g ≫ α) =
      ((sheafToPresheaf J E).map ((G.sheafPushforwardContinuous E J K).map α)).app
        (Opposite.op A) (lhsEquiv' H g)
    simp only [lhsEquiv', Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_right (adj := G.sheafAdjunctionContinuous E J K),
      Adjunction.homEquiv_naturality_right (adj := sheafificationAdjunction J E),
      uliftYonedaEquiv_comp]
  have rhsNaturality (H H' : Sheaf K E) (α : H ⟶ H') (g : Q ⟶ H) :
      rhsEquiv H' (g ≫ α) = (α.hom.app (Opposite.op (G.obj A))) (rhsEquiv H g) := by
    simp only [rhsEquiv, Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_right (adj := sheafificationAdjunction K E),
      uliftYonedaEquiv_comp]
    rfl
  let corepNatIso : coyoneda.obj (Opposite.op P) ≅ coyoneda.obj (Opposite.op Q) :=
    NatIso.ofComponents (fun H => Equiv.toIso ((lhsEquiv H).trans (rhsEquiv H).symm)) (by
      intro H H' α
      ext g
      change (rhsEquiv H').symm (lhsEquiv H' (g ≫ α)) = (rhsEquiv H).symm (lhsEquiv H g) ≫ α
      apply (rhsEquiv H').injective
      rw [Equiv.apply_symm_apply, lhsNaturality, rhsNaturality, Equiv.apply_symm_apply])
  exact ((Coyoneda.fullyFaithful (C := Sheaf K E)).preimageIso corepNatIso).unop.symm

/-! ### Factoring through an open -/

/-- Two morphisms out of a terminal object are equal exactly when their equalizer is itself
terminal. -/
private theorem equalizer_isTerminal_iff_eq {C : Type*} [Category C] [HasEqualizers C]
    {X F : C} (hX : IsTerminal X) (s t : X ⟶ F) :
    s = t ↔ Nonempty (IsTerminal (equalizer s t)) := by
  refine ⟨?_, fun ⟨hE⟩ => ?_⟩
  · rintro rfl
    exact ⟨hX.ofIso (asIso (equalizer.ι s s)).symm⟩
  · have : IsIso (equalizer.ι s t) := isIso_of_isTerminal hE hX _
    exact (cancel_epi (equalizer.ι s t)).1 (equalizer.condition s t)

/-- The base change of an open subscheme of `S` is the final object of the small étale site of
`T` exactly when the structure morphism of `T` factors through that open. -/
private theorem pullbackOpen_isTerminal_iff_factors (S T : B.Scheme)
    (W : (B.inclusion.obj S).Opens) (f : T ⟶ S) :
    Nonempty (IsTerminal ((smallEtaleBaseChange B f).obj
        ((opensToBoundedEtale B S.obj S.property).obj W))) ↔
      ∃ g : B.inclusion.obj T ⟶ W.toScheme, g ≫ W.ι = B.inclusion.map f := by
  let A := (smallEtaleBaseChange B f).obj ((opensToBoundedEtale B S.obj S.property).obj W)
  let j := SmallEtale.inclusion B T.obj T.property
  let i : ((opensToBoundedEtale B S.obj S.property).obj W).obj.left ⟶ S :=
    ((opensToBoundedEtale B S.obj S.property).obj W).obj.hom
  have : B.inclusion.Full := ObjectProperty.full_ι _
  have : B.inclusion.Faithful := ObjectProperty.faithful_ι _
  have : j.Full := ObjectProperty.full_ι _
  have : j.Faithful := ObjectProperty.faithful_ι _
  have hi : B.inclusion.map i = W.ι := rfl
  have : Mono i := Functor.ReflectsMonomorphisms.reflects (F := B.inclusion) i
    (inferInstanceAs (Mono W.ι))
  have hAobj : A.obj = (Over.pullback f).obj (Over.mk i) := by
    change ((smallEtaleBaseChange B f).obj
      ((opensToBoundedEtale B S.obj S.property).obj W)).obj = _
    rw [smallEtaleBaseChange_obj_obj]
    rfl
  have : Mono A.obj.hom := by
    rw [hAobj]
    dsimp [Over.pullback]
    infer_instance
  have hsub : IsSubterminal A := IsSubterminal.def.2 fun _ p q =>
    j.map_injective <| Over.OverMorphism.ext <|
      (cancel_mono A.obj.hom).1 ((Over.w (j.map p)).trans (Over.w (j.map q)).symm)
  constructor
  · rintro ⟨hA⟩
    let qOver : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj (Over.mk i) :=
      hAobj ▸ j.map (hA.from (SmallEtale.final B T.obj T.property))
    let qBase := ((Over.mapPullbackAdj f).homEquiv _ _).symm qOver
    have hfac : qBase.left ≫ i = f := by simpa using Over.w qBase
    exact ⟨B.inclusion.map qBase.left, by
      rw [← hi]
      exact (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map hfac)⟩
  · rintro ⟨g, hg⟩
    let FF := Functor.FullyFaithful.ofFullyFaithful B.inclusion
    let g' : T ⟶ ((opensToBoundedEtale B S.obj S.property).obj W).obj.left :=
      FF.preimage (show B.inclusion.obj T ⟶
        B.inclusion.obj ((opensToBoundedEtale B S.obj S.property).obj W).obj.left from g)
    have hg' : g' ≫ i = f :=
      B.inclusion.map_injective (by rwa [Functor.map_comp, FF.map_preimage, hi])
    let qOver := (Over.mapPullbackAdj f).homEquiv _ _ (Over.homMk g' hg' :
      (Over.map f).obj (Over.mk (𝟙 T)) ⟶ Over.mk i)
    let q' : j.obj (SmallEtale.final B T.obj T.property) ⟶ j.obj A := hAobj ▸ qOver
    let h := (Functor.FullyFaithful.ofFullyFaithful j).preimage q'
    have : ∀ X : SmallEtale B T.obj T.property, Unique (X ⟶ A) := fun X =>
      ⟨⟨(SmallEtale.finalIsTerminal B T.obj T.property).from X ≫ h⟩, fun k => hsub k _⟩
    exact ⟨IsTerminal.ofUnique A⟩

/-! ### The equality locus -/

section Locus

variable (S T : B.Scheme)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (max (u + 1) v)))
    (s t : terminal (Sheaf (SmallEtale.topology B S.obj S.property)
      (Type (max (u + 1) v))) ⟶ F)

/-- Inverse image along a morphism of the big étale site, between the small étale topoi.

This is the functor `f_small^{-1}` on sheaves of sets, taken in Mathlib's explicit sheaf-pullback
construction so that its left exactness is available from the construction. -/
@[sga "4½ Arcata 2.3.3"]
public abbrev smallEtalePullback (f : T ⟶ S) :
    Sheaf (SmallEtale.topology B S.obj S.property) (Type (max (u + 1) v)) ⥤
      Sheaf (SmallEtale.topology B T.obj T.property) (Type (max (u + 1) v)) :=
  Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange B f)
    (Type (max (u + 1) v)) (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)

/-- Two global sections of a sheaf on the small étale site of `S` agree after inverse image
along `f : T ⟶ S` exactly when `T` factors through the open representing their equalizer.

Inverse image preserves finite limits, so it carries the equalizer of the two sections to the
equalizer of their restrictions; that equalizer is the final sheaf exactly when the restrictions
agree, and the base change of the representing open is final exactly when `T` factors through
it. -/
private theorem pullback_sections_equal_iff_factors_open (f : T ⟶ S) :
    (smallEtalePullback B S T f).map s = (smallEtalePullback B S T f).map t ↔
      ∃ g : B.inclusion.obj T ⟶ (equalizerOpen.{u, v} B S F s t).toScheme,
        g ≫ (equalizerOpen.{u, v} B S F s t).ι = B.inclusion.map f := by
  let JS := SmallEtale.topology B S.obj S.property
  let JT := SmallEtale.topology B T.obj T.property
  let G := smallEtaleBaseChange B f
  let L := smallEtalePullback B S T f
  let E := equalizer s t
  have : G.IsContinuous JS JT := smallEtaleBaseChange_isContinuous B f
  have : PreservesFiniteLimits (G.op.lan :
      ((SmallEtale B S.obj S.property)ᵒᵖ ⥤ Type (max (u + 1) v)) ⥤
        (SmallEtale B T.obj T.property)ᵒᵖ ⥤ Type (max (u + 1) v)) :=
    lan_preservesFiniteLimits_of_representablyFlat G
  have : PreservesFiniteLimits (G.sheafPullback (Type (max (u + 1) v)) JS JT) :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits G (Type (max (u + 1) v)) JS JT
  have : PreservesFiniteLimits L :=
    preservesFiniteLimits_of_natIso
      (Functor.sheafPullbackConstruction.sheafPullbackIso G (Type (max (u + 1) v)) JS JT)
  let W := equalizerOpen.{u, v} B S F s t
  let A := (opensToBoundedEtale B S.obj S.property).obj W
  obtain ⟨eEW⟩ := equalizerOpen_representation.{u, v} B S F s t
  let eEA : E ≅ (presheafToSheaf JS (Type (max (u + 1) v))).obj
      ((uliftYoneda.{max (u + 1) v} (C := SmallEtale B S.obj S.property)).obj A) :=
    eEW ≪≫ openSheafificationIso.{u, v} B S W
  let eLE : L.obj E ≅ (presheafToSheaf JT (Type (max (u + 1) v))).obj
      ((uliftYoneda.{max (u + 1) v} (C := SmallEtale B T.obj T.property)).obj (G.obj A)) :=
    L.mapIso eEA ≪≫
      ((Functor.sheafPullbackConstruction.sheafPullbackIso G
        (Type (max (u + 1) v)) JS JT).app _).symm ≪≫
      sheafPullbackUliftYonedaIso.{u, v} G JS JT A
  have hEqTerm : L.map s = L.map t ↔ Nonempty (IsTerminal (L.obj E)) :=
    (equalizer_isTerminal_iff_eq (IsTerminal.isTerminalObj L _ terminalIsTerminal) _ _).trans
      (Equiv.nonempty_congr (IsTerminal.equivOfIso (PreservesEqualizer.iso L s t).symm))
  have hRepTerm := Equiv.nonempty_congr (IsTerminal.equivOfIso eLE)
  exact hEqTerm.trans (hRepTerm.trans
    ((representableSheafification_isTerminal_iff.{u, v} B T (G.obj A)).trans
      (pullbackOpen_isTerminal_iff_factors B S T W f)))

/-- **Stacks 09XM, the open locus.** The largest open subscheme of `S` on which two global
sections of a sheaf on the small étale site of `S` agree: the supremum of the opens through
which only agreeing morphisms factor. -/
@[stacks 09XM "open locus"]
public def openEqLocus : (B.inclusion.obj S).Opens :=
  sSup { V : (B.inclusion.obj S).Opens |
    ∀ (T : B.Scheme) (f : T ⟶ S),
      (∃ g : B.inclusion.obj T ⟶ V.toScheme, g ≫ V.ι = B.inclusion.map f) →
        (smallEtalePullback B S T f).map s =
          (smallEtalePullback B S T f).map t }

/-- The open equality locus is the open representing the equalizer of the two sections. -/
private theorem openEqLocus_eq_equalizerOpen :
    openEqLocus B S F s t = equalizerOpen.{u, v} B S F s t := by
  apply le_antisymm
  · apply sSup_le
    intro V hV
    let V₀ : B.Scheme :=
      ⟨(V : Scheme), (Scheme.size_coe_opens_le (B.inclusion.obj S) V).trans_lt S.property⟩
    let i : V₀ ⟶ S := ObjectProperty.homMk V.ι
    obtain ⟨g, hg⟩ := (pullback_sections_equal_iff_factors_open.{u, v} B S V₀ F s t i).mp
      (hV V₀ i ⟨𝟙 _, Category.id_comp _⟩)
    intro x hx
    have hraw : (equalizerOpen.{u, v} B S F s t).ι (g ⟨x, hx⟩) = V.ι ⟨x, hx⟩ :=
      congrArg (fun k : B.inclusion.obj V₀ ⟶ B.inclusion.obj S => k ⟨x, hx⟩) hg
    change x ∈ (equalizerOpen.{u, v} B S F s t : Set (B.inclusion.obj S))
    rw [← show V.ι ⟨x, hx⟩ = x from rfl, ← hraw]
    exact (g ⟨x, hx⟩).property
  · exact le_sSup fun T f => (pullback_sections_equal_iff_factors_open.{u, v} B S T F s t f).mpr

/-- **Stacks 09XM, the universal property.** A morphism of the big étale site factors through
the open equality locus exactly when the two sections agree after inverse image along the
induced morphism of small étale topoi. -/
@[stacks 09XM "universal property"]
public theorem factorsThrough_openEqLocus_iff (f : T ⟶ S) :
    (∃ g : B.inclusion.obj T ⟶ (openEqLocus B S F s t).toScheme,
      g ≫ (openEqLocus B S F s t).ι = B.inclusion.map f) ↔
      (smallEtalePullback B S T f).map s =
        (smallEtalePullback B S T f).map t := by
  rw [openEqLocus_eq_equalizerOpen.{u, v} B S F s t]
  exact (pullback_sections_equal_iff_factors_open.{u, v} B S T F s t f).symm

end Locus

end AlgebraicGeometry

end
