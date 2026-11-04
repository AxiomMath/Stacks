module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackModel
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.LeftKanExtensionExactness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The open locus where two global sections of a sheaf on a space agree

Let `X` be a topological space, let `G` be a sheaf of sets on `X` and let `s` and `t` be two
global sections of `G`, presented as morphisms out of a terminal sheaf. There is a largest open
`W ⊆ X` on which `s` and `t` agree, and for a continuous map `f : Y ⟶ X` the inverse images of
`s` and `t` along `f` agree exactly when `f⁻¹W` is all of `Y`.

## Main definitions

* `Stacks.OpenEqLocus.opensSheaf` — the sheaf of sets on `X` represented by an open.
* `Stacks.OpenEqLocus.eqLocus` — the largest open on which two global sections agree.

## Main results

* `Stacks.OpenEqLocus.opensSheafHomEquiv` — morphisms from the sheaf represented by an open are
  the sections over that open.
* `Stacks.OpenEqLocus.le_eqLocus_iff` — the universal property of the locus on opens.
* `Stacks.OpenEqLocus.eq_iff_eqLocus_eq_top` — the locus is everything exactly when the two
  sections agree.
* `Stacks.OpenEqLocus.sheafPullback_map_eq_iff` — two global sections agree after inverse image
  along `f` exactly when `f⁻¹` of their locus is everything.

## References

* [Stacks Project, Tag 09XM](https://stacks.math.columbia.edu/tag/09XM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.OpenEqLocus

/-! ### Naturally isomorphic functors identify the same pairs of morphisms -/

/-- Naturally isomorphic functors agree on which pairs of parallel morphisms they identify. -/
public theorem map_eq_iff_of_natIso {C : Type*} [Category* C] {D : Type*} [Category* D]
    {P Q : C ⥤ D} (i : P ≅ Q) {A A' : C} {σ₁ σ₂ : A ⟶ A'} :
    P.map σ₁ = P.map σ₂ ↔ Q.map σ₁ = Q.map σ₂ := by
  have key : ∀ {R R' : C ⥤ D} (j : R ≅ R'), R.map σ₁ = R.map σ₂ → R'.map σ₁ = R'.map σ₂ := by
    intro R R' j h
    have h1 := j.hom.naturality σ₁
    rw [h, j.hom.naturality σ₂] at h1
    exact (cancel_epi (j.hom.app A)).mp h1.symm
  exact ⟨key i, key i.symm⟩

/-! ### The sheaf represented by an open -/

section Represented

variable {X : TopCat.{u}}

/-- Sections of the Yoneda presheaf of an open are the inclusions of opens. -/
public def yonedaSectionEquiv (W : Opens X) (V : (Opens X)ᵒᵖ) :
    (uliftYoneda.{u + 1}.obj W).obj V ≃ (V.unop ⟶ W) := Equiv.ulift

/-- All sections of the Yoneda presheaf of an open over a fixed open are equal. -/
public theorem yonedaSection_ext {W : Opens X} {V : (Opens X)ᵒᵖ}
    (a b : (uliftYoneda.{u + 1}.obj W).obj V) : a = b :=
  (yonedaSectionEquiv W V).injective (Subsingleton.elim _ _)

/-- **The presheaf represented by an open is a sheaf.** -/
public theorem isSheaf_uliftYoneda_opens (W : Opens X) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (uliftYoneda.{u + 1}.obj W) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro V R hR x _
  have hVW : V ≤ W := by
    intro p hp
    obtain ⟨V', g, hg, hp'⟩ := hR p hp
    exact leOfHom (yonedaSectionEquiv W (op V') (x g hg)) hp'
  exact ⟨(yonedaSectionEquiv W (op V)).symm (homOfLE hVW),
    fun _ _ _ => yonedaSection_ext _ _, fun _ _ => yonedaSection_ext _ _⟩

/-- The sheaf of sets on `X` represented by an open `W`. -/
public abbrev opensSheaf (W : Opens X) :
    Sheaf (Opens.grothendieckTopology X) (Type (u + 1)) :=
  ⟨uliftYoneda.{u + 1}.obj W, isSheaf_uliftYoneda_opens W⟩

/-- All sections of the sheaf represented by an open over a fixed open are equal. -/
public theorem opensSheaf_ext {W : Opens X} {V : (Opens X)ᵒᵖ}
    (a b : (opensSheaf W).obj.obj V) : a = b := yonedaSection_ext a b

/-- The tautological section of the sheaf represented by `W` over `W` itself. -/
public def opensSheafSelf (W : Opens X) : (opensSheaf W).obj.obj (op W) :=
  (yonedaSectionEquiv W (op W)).symm (𝟙 W)

/-- A section of the sheaf represented by `W` over `V` is a witness that `V ≤ W`. -/
public theorem le_of_opensSheaf_section {W V : Opens X}
    (a : (opensSheaf W).obj.obj (op V)) : V ≤ W :=
  leOfHom (yonedaSectionEquiv W (op V) a)

/-- **Sections of a sheaf over an open are the morphisms out of the sheaf that open
represents.** -/
public def opensSheafHomEquiv (W : Opens X)
    (K : Sheaf (Opens.grothendieckTopology X) (Type (u + 1))) :
    (opensSheaf W ⟶ K) ≃ K.obj.obj (op W) :=
  Sheaf.homEquiv.trans uliftYonedaEquiv.{u + 1}

/-- Post-composition is computed on sections by the component of the morphism. -/
public theorem opensSheafHomEquiv_comp (W : Opens X)
    {K K' : Sheaf (Opens.grothendieckTopology X) (Type (u + 1))} (φ : opensSheaf W ⟶ K)
    (ψ : K ⟶ K') :
    (opensSheafHomEquiv W K') (φ ≫ ψ) = ψ.hom.app (op W) ((opensSheafHomEquiv W K) φ) := rfl

/-- If there is at most one morphism from the sheaf represented by `V` to `K`, then `K` has at
most one section over `V`. -/
private theorem subsingleton_sections_of_subsingleton_hom
    {K : Sheaf (Opens.grothendieckTopology X) (Type (u + 1))} (V : Opens X)
    (h : Subsingleton (opensSheaf V ⟶ K)) : Subsingleton (K.obj.obj (op V)) :=
  Equiv.subsingleton (opensSheafHomEquiv V K).symm

/-- A terminal sheaf of sets on `X` has at most one section over every open. -/
public theorem subsingleton_sections_of_isTerminal
    {A : Sheaf (Opens.grothendieckTopology X) (Type (u + 1))} (hA : IsTerminal A)
    (V : Opens X) : Subsingleton (A.obj.obj (op V)) :=
  subsingleton_sections_of_subsingleton_hom V ⟨fun p q => hA.hom_ext p q⟩

/-- A sheaf with subsingleton sections over every open and a global section is terminal. -/
public def isTerminal_of_subsingleton_of_section
    {Z : Sheaf (Opens.grothendieckTopology X) (Type (u + 1))}
    (hsub : ∀ V : (Opens X)ᵒᵖ, Subsingleton (Z.obj.obj V))
    (hsec : Nonempty (Z.obj.obj (op (⊤ : Opens X)))) : IsTerminal Z := by
  haveI huniq : ∀ H : Sheaf (Opens.grothendieckTopology X) (Type (u + 1)), Unique (H ⟶ Z) := by
    intro H
    refine ⟨⟨ObjectProperty.homMk
      { app := fun V => ↾fun _ =>
          Z.obj.map (homOfLE (le_top (a := V.unop))).op hsec.some
        naturality := by
          intro V₁ V₂ g
          ext a
          exact (hsub V₂).elim _ _ }⟩, fun m => ?_⟩
    refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
    ext a
    exact (hsub V).elim _ _
  exact IsTerminal.ofUnique Z

end Represented

/-! ### Equalizers over a terminal object -/

section Equalizers

variable {C : Type*} [Category* C] [HasEqualizers C] {A G : C}

/-- Two morphisms out of a terminal object are equal exactly when their equalizer is itself
terminal. -/
public theorem equalizer_isTerminal_iff_eq (hA : IsTerminal A) (s t : A ⟶ G) :
    s = t ↔ Nonempty (IsTerminal (equalizer s t)) := by
  constructor
  · intro h
    have huniq : ∀ Z : C, Unique (Z ⟶ equalizer s t) := fun Z => by
      have hcond : hA.from Z ≫ s = hA.from Z ≫ t := by rw [h]
      exact ⟨⟨equalizer.lift (hA.from Z) hcond⟩, fun m => (cancel_mono (equalizer.ι s t)).1
        ((hA.hom_ext _ _).trans (equalizer.lift_ι (hA.from Z) hcond).symm)⟩
    exact ⟨IsTerminal.ofUnique (equalizer s t)⟩
  · rintro ⟨hE⟩
    have : IsIso (equalizer.ι s t) := isIso_of_isTerminal hE hA _
    exact (cancel_epi (equalizer.ι s t)).1 (equalizer.condition s t)

/-- There is at most one morphism into the equalizer of two morphisms out of a terminal
object. -/
public theorem subsingleton_hom_equalizer (hA : IsTerminal A) (s t : A ⟶ G) (Z : C) :
    Subsingleton (Z ⟶ equalizer s t) :=
  ⟨fun _ _ => (cancel_mono (equalizer.ι s t)).1 (hA.hom_ext _ _)⟩

/-- A morphism into the equalizer of two morphisms out of a terminal object exists exactly when
the two morphisms agree after the unique morphism to the terminal object. -/
public theorem nonempty_hom_equalizer_iff (hA : IsTerminal A) (s t : A ⟶ G) (Z : C) :
    Nonempty (Z ⟶ equalizer s t) ↔ hA.from Z ≫ s = hA.from Z ≫ t := by
  constructor
  · rintro ⟨m⟩
    have hm : m ≫ equalizer.ι s t = hA.from Z := hA.hom_ext _ _
    rw [← hm, Category.assoc, Category.assoc, equalizer.condition]
  · exact fun h => ⟨equalizer.lift (hA.from Z) h⟩

end Equalizers

/-! ### The equality locus -/

section Locus

variable {X : TopCat.{u}}
  {A G : Sheaf (Opens.grothendieckTopology X) (Type (u + 1))}

/-- **The open locus where two global sections agree**: the supremum of the opens over which the
two morphisms have the same component. -/
public def eqLocus (s t : A ⟶ G) : Opens X :=
  sSup { V : Opens X | s.hom.app (op V) = t.hom.app (op V) }

/-- Two morphisms out of a terminal sheaf agree after the unique morphism from the sheaf
represented by `V` exactly when their components at `V` agree. -/
private theorem comp_from_eq_iff (hA : IsTerminal A) (s t : A ⟶ G) (V : Opens X) :
    hA.from (opensSheaf V) ≫ s = hA.from (opensSheaf V) ≫ t ↔
      s.hom.app (op V) = t.hom.app (op V) := by
  have := subsingleton_sections_of_isTerminal hA V
  constructor
  · intro h
    have h1 := (opensSheafHomEquiv_comp V (hA.from (opensSheaf V)) s).symm.trans
      ((congrArg (opensSheafHomEquiv V G) h).trans
        (opensSheafHomEquiv_comp V (hA.from (opensSheaf V)) t))
    ext a
    rw [Subsingleton.elim a ((opensSheafHomEquiv V A) (hA.from (opensSheaf V)))]
    exact h1
  · intro h
    refine (opensSheafHomEquiv V G).injective ?_
    rw [opensSheafHomEquiv_comp, opensSheafHomEquiv_comp, h]

/-- The equalizer of two global sections has subsingleton sections. -/
public theorem subsingleton_equalizer_sections (hA : IsTerminal A) (s t : A ⟶ G)
    (V : (Opens X)ᵒᵖ) : Subsingleton ((equalizer s t).obj.obj V) :=
  subsingleton_sections_of_subsingleton_hom V.unop (subsingleton_hom_equalizer hA s t _)

/-- A section of the equalizer over `V` exists exactly when the two morphisms have the same
component at `V`. -/
public theorem nonempty_equalizer_sections_iff (hA : IsTerminal A) (s t : A ⟶ G) (V : Opens X) :
    Nonempty ((equalizer s t).obj.obj (op V)) ↔ s.hom.app (op V) = t.hom.app (op V) := by
  rw [← Equiv.nonempty_congr (opensSheafHomEquiv V (equalizer s t)),
    nonempty_hom_equalizer_iff hA s t, comp_from_eq_iff hA s t V]

/-- **The universal property of the equality locus on opens.** The two morphisms have the same
component at `V` exactly when `V` is contained in their equality locus. -/
public theorem le_eqLocus_iff (hA : IsTerminal A) (s t : A ⟶ G) (V : Opens X) :
    s.hom.app (op V) = t.hom.app (op V) ↔ V ≤ eqLocus s t := by
  refine ⟨fun h => le_sSup h, fun hV => ?_⟩
  have := subsingleton_equalizer_sections hA s t
  refine (nonempty_equalizer_sections_iff hA s t V).mp ?_
  let R : Sieve V :=
    { arrows := fun V' _ => Nonempty ((equalizer s t).obj.obj (op V'))
      downward_closed := fun hk g => ⟨(equalizer s t).obj.map g.op hk.some⟩ }
  have hR : R ∈ Opens.grothendieckTopology X V := by
    intro p hp
    obtain ⟨V₀, hV₀, hp₀⟩ := Opens.mem_sSup.mp (hV hp)
    exact ⟨V ⊓ V₀, homOfLE inf_le_left, ⟨(equalizer s t).obj.map
      (homOfLE (inf_le_right : V ⊓ V₀ ≤ V₀)).op
        ((nonempty_equalizer_sections_iff hA s t V₀).mpr hV₀).some⟩, ⟨hp, hp₀⟩⟩
  have hsheaf : Presieve.IsSheaf (Opens.grothendieckTopology X) (equalizer s t).obj :=
    (isSheaf_iff_isSheaf_of_type _ _).mp (equalizer s t).property
  have hfam : Presieve.FamilyOfElements (equalizer s t).obj R.arrows :=
    fun _ _ hg => hg.some
  have hcompat : hfam.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ _
    exact Subsingleton.elim _ _
  obtain ⟨a, -⟩ := hsheaf R hR hfam hcompat
  exact ⟨a⟩

/-- **The equality locus is everything exactly when the two sections agree.** -/
public theorem eq_iff_eqLocus_eq_top (hA : IsTerminal A) (s t : A ⟶ G) :
    s = t ↔ eqLocus s t = ⊤ := by
  constructor
  · rintro rfl
    exact top_le_iff.mp (le_sSup rfl)
  · intro h
    exact Sheaf.hom_ext (NatTrans.ext (funext fun V =>
      (le_eqLocus_iff hA s t V.unop).mpr (h ▸ le_top)))

end Locus

/-! ### Inverse image along a continuous map -/

section Pullback

variable {X Y : TopCat.{u}} (f : Y ⟶ X)

/-- The inverse image of sheaves of sets along a continuous map, as the sheaf-level left adjoint
of restriction along `TopologicalSpace.Opens.map f`. -/
public abbrev opensPullback :
    Sheaf (Opens.grothendieckTopology X) (Type (u + 1)) ⥤
      Sheaf (Opens.grothendieckTopology Y) (Type (u + 1)) :=
  (Opens.map f).sheafPullback (Type (u + 1)) (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y)

/-- The adjunction between inverse image and restriction along `TopologicalSpace.Opens.map f`. -/
public abbrev opensPullbackAdj :
    opensPullback f ⊣ (Opens.map f).sheafPushforwardContinuous (Type (u + 1))
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) :=
  (Opens.map f).sheafAdjunctionContinuous (Type (u + 1)) (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y)

/-- **Inverse image along a continuous map is left exact.** -/
@[sga "4 III 1.3" "Clause 5, special case", sga "4 III 1.9.1"]
public instance preservesFiniteLimits_opensPullback :
    PreservesFiniteLimits (opensPullback f) := by
  have : PreservesFiniteLimits ((Opens.map f).op.lan :
      ((Opens X)ᵒᵖ ⥤ Type (u + 1)) ⥤ (Opens Y)ᵒᵖ ⥤ Type (u + 1)) :=
    CategoryTheory.lan_preservesFiniteLimits_of_representablyFlat.{u, u, u + 1, u, u}
      (Opens.map f)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

variable {A G : Sheaf (Opens.grothendieckTopology X) (Type (u + 1))} (s t : A ⟶ G)

/-- Inverse image carries the equalizer of two global sections to the equalizer of their inverse
images. -/
public def opensPullbackEqualizerIso :
    (opensPullback f).obj (equalizer s t) ≅
      equalizer ((opensPullback f).map s) ((opensPullback f).map t) := by
  let L := opensPullback f
  have hLim : IsLimit (L.mapCone (limit.cone (parallelPair s t))) :=
    isLimitOfPreserves L (limit.isLimit (parallelPair s t))
  let eDiag : parallelPair s t ⋙ L ≅ parallelPair (L.map s) (L.map t) :=
    NatIso.ofComponents (fun j => eqToIso (by cases j <;> rfl)) (by
      intro i j g
      cases g <;> simp)
  have hLim' : IsLimit ((Cone.postcompose eDiag.hom).obj
      (L.mapCone (limit.cone (parallelPair s t)))) :=
    (IsLimit.postcomposeHomEquiv eDiag (L.mapCone (limit.cone (parallelPair s t)))).symm hLim
  exact hLim'.conePointUniqueUpToIso (limit.isLimit (parallelPair (L.map s) (L.map t)))

/-- The comparison of the inverse image of the equalizer with the sheaf represented by the
inverse image of the equality locus: a section of the equalizer over `V` forces `V` to lie in
the locus, hence `f⁻¹V` to lie in `f⁻¹` of the locus. -/
public def opensPullbackEqualizerToLocus (hA : IsTerminal A) :
    (opensPullback f).obj (equalizer s t) ⟶
      opensSheaf ((Opens.map f).obj (eqLocus s t)) :=
  ((opensPullbackAdj f).homEquiv _ _).symm <| ObjectProperty.homMk
    { app := fun V => ↾fun a =>
        (yonedaSectionEquiv ((Opens.map f).obj (eqLocus s t))
          (op ((Opens.map f).obj V.unop))).symm
          (homOfLE (fun _ hp => (le_eqLocus_iff hA s t V.unop).mp
            ((nonempty_equalizer_sections_iff hA s t V.unop).mp ⟨a⟩) hp))
      naturality := by
        intro V₁ V₂ g
        ext a
        exact yonedaSection_ext _ _ }

/-- The inverse image of the equalizer has subsingleton sections over every open. -/
private theorem subsingleton_opensPullback_equalizer_sections (hA : IsTerminal A)
    (V : (Opens Y)ᵒᵖ) :
    Subsingleton (((opensPullback f).obj (equalizer s t)).obj.obj V) := by
  have := subsingleton_hom_equalizer (IsTerminal.isTerminalObj (opensPullback f) _ hA)
    ((opensPullback f).map s) ((opensPullback f).map t) (opensSheaf V.unop)
  exact subsingleton_sections_of_subsingleton_hom V.unop
    (Equiv.subsingleton (Iso.homCongr (Iso.refl _) (opensPullbackEqualizerIso f s t)))

/-- **Two global sections agree after inverse image along `f` exactly when the inverse image of
their equality locus is everything.** -/
public theorem sheafPullback_map_eq_iff (hA : IsTerminal A) :
    (opensPullback f).map s = (opensPullback f).map t ↔
      (Opens.map f).obj (eqLocus s t) = ⊤ := by
  have hLA : IsTerminal ((opensPullback f).obj A) :=
    IsTerminal.isTerminalObj (opensPullback f) _ hA
  rw [equalizer_isTerminal_iff_eq hLA]
  constructor
  · rintro ⟨hterm⟩
    have hterm' : IsTerminal ((opensPullback f).obj (equalizer s t)) :=
      hterm.ofIso (opensPullbackEqualizerIso f s t).symm
    have h0 : ((opensPullback f).obj (equalizer s t)).obj.obj (op (⊤ : Opens Y)) :=
      opensSheafHomEquiv (⊤ : Opens Y) _ (hterm'.from (opensSheaf (⊤ : Opens Y)))
    exact top_le_iff.mp (le_of_opensSheaf_section
      ((opensPullbackEqualizerToLocus f s t hA).hom.app (op (⊤ : Opens Y)) h0))
  · intro htop
    refine ⟨(isTerminal_of_subsingleton_of_section
      (subsingleton_opensPullback_equalizer_sections f s t hA) ?_).ofIso
      (opensPullbackEqualizerIso f s t)⟩
    have hloc : ((equalizer s t).obj.obj (op (eqLocus s t))) :=
      ((nonempty_equalizer_sections_iff hA s t _).mpr
        ((le_eqLocus_iff hA s t _).mpr (le_refl _))).some
    rw [← htop]
    exact ⟨((opensPullbackAdj f).unit.app (equalizer s t)).hom.app
      (op (eqLocus s t)) hloc⟩

end Pullback

end Stacks.OpenEqLocus

end
