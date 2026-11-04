module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionDiagonalTransport
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionDiagonalRepresent
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsDiagonalAffineLfp
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingFunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Basic
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleSheafPropertyUnconditional
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizerRepresents

/-!
# The bootstrap for the diagonal of Artin's contraction functor

Remark **Stacks 0GIC** observes that the representability of the diagonal `Δ : F ⟶ F × F` of
Artin's functor (Stacks 0GHA) needs no separatedness of `X'` or `W`: for two elements of `F(V)`
the triple `E'`, `(E' ⟶ V)⁻¹Z`, `E'_{/Z} ⟶ E_W` of Stacks 0GHD (4) is a situation over `V` in
which `E' ⟶ V` and `E_W ⟶ V` are separated, Artin's theorem (Stacks 0GIB) in the separated case
gives it a solution `E ⟶ V`, and `E` represents `F ×_{Δ, F × F} V` (Stacks 0GHD, final
conclusion). This file proves the pieces of that argument which do not involve Stacks 0GIB.

* The local rings at the finite type points of a scheme locally of finite type over `S` are
  G-rings when those of `S` are (Stacks 02J3 and 07PV), so Stacks 0GIB applies over such `V`.
* The triple of Stacks 0GHD (4) is separated over `V`: `E' ⟶ V` is separated (Stacks 0GHD), and
  so is the algebraic space of the situation over `V` attached to it; `E_W ⟶ V` is a
  monomorphism, and so is the formal algebraic space over `V` attached to it.
* A limit preserving algebraic space `E` over `V` representing `F ×_{Δ, F × F} V` on the locally
  Noetherian schemes over `V` is a scheme: its values on locally Noetherian schemes are
  subsingletons, hence all its values are, so `E ⟶ V` is a monomorphism locally of finite type,
  hence separated and locally quasi-finite (Stacks 0463), hence representable (Stacks 0418). So
  the equalizer of the two elements of `F(V)` is represented by a morphism of schemes
  `e : b ⟶ V` locally of finite type.

## Main results

* `AlgebraicGeometry.isGRing_stalk_of_locallyOfFiniteType`.
* `AlgebraicGeometry.Artin.ContractionEqualizer.isSeparated_terminal_from` and
  `AlgebraicGeometry.Artin.ContractionEqualizer.isSeparatedMorphism_terminal_from_W`.
* `AlgebraicGeometry.Artin.ContractionEqualizer.exists_factors_iff_of_limitPreserving`.

## References

* [Stacks Project, Tag 02J3](https://stacks.math.columbia.edu/tag/02J3)
* [Stacks Project, Tag 0418](https://stacks.math.columbia.edu/tag/0418)
* [Stacks Project, Tag 0463](https://stacks.math.columbia.edu/tag/0463)
* [Stacks Project, Tag 07PV](https://stacks.math.columbia.edu/tag/07PV)
* [Stacks Project, Tag 0GHD](https://stacks.math.columbia.edu/tag/0GHD)
* [Stacks Project, Tag 0GIC](https://stacks.math.columbia.edu/tag/0GIC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **G-rings at finite type points ascend along morphisms locally of finite type.** If the local
rings of `S` at its finite type points are G-rings and `f : V ⟶ S` is locally of finite type, then
the local rings of `V` at its finite type points are G-rings: a finite type point `v` of `V` maps
to a finite type point of `S` (Stacks 02J3), and `𝒪_{V, v}` is essentially of finite type over
`𝒪_{S, f v}` (Stacks 07PV). -/
theorem isGRing_stalk_of_locallyOfFiniteType {V S : Scheme.{u}} (f : V ⟶ S)
    [LocallyOfFiniteType f]
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s))
    (v : V) (hv : IsFiniteTypePoint v) : IsGRing (V.presheaf.stalk v) := by
  have h : IsFiniteTypePoint (f v) := mapsTo_finiteTypePoints f hv
  let := (f.stalkMap v).hom.toAlgebra
  have : Algebra.EssFiniteType (S.presheaf.stalk (f v)) (V.presheaf.stalk v) :=
    LocallyOfFiniteType.stalkMap f v
  exact isGRing_of_essFiniteType (hG _ h)

namespace Space

variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)

/-- **Separatedness over a smaller base.** A morphism of algebraic spaces over the representable
presheaf of `g : V ⟶ S` whose underlying morphism is separated over `S` induces a separated
morphism of the attached algebraic spaces over `V` (Stacks 04SG together with
`AlgebraicGeometry.Space.isSeparated_of_relocalize`). -/
theorem isSeparated_smallerBaseInverse_map
    {X Y : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X.left) (hf : IsSeparated B S hS f.left) :
    IsSeparated B V hV ((smallerBasePresheafEquivalence B V S hV hS g).inverse.map f) := by
  refine isSeparated_of_relocalize B V hV hS g (relativelyRepresentable_pullbackDiagonal B V hV _
    (isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B V S hV hS g X hX)) ?_
  refine isSeparated_of_arrowIso B S hS f.left _
    (smallerBaseInverseRelocalizeIso B V S hV hS g X).inv
    (smallerBaseInverseRelocalizeIso B V S hV hS g Y).inv ?_ hf
  rw [Iso.inv_comp_eq, ← Category.assoc, ← smallerBaseInverseRelocalizeIso_hom_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Space

namespace Artin.ContractionEqualizer

open ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {c : ContractionSituation B S hS} {V : BigFppfOver B S hS}
    (d : ContractionEqualizer c V)

/-- **The algebraic space of the triple of Stacks 0GHD (4) is separated over `V`**, because
`E' ⟶ V` is separated (Stacks 0GHD). No separatedness of `X'` or `W` is used. -/
theorem isSeparated_terminal_from (hVN : IsLocallyNoetherian V.left.obj) :
    Space.IsSeparated B V.left.obj V.left.property (terminal.from (d.situation hVN).X') := by
  rw [d.terminal_from_eq hVN]
  have := Space.isSeparated_respectsIso B V.left.obj V.left.property
  exact (MorphismProperty.cancel_right_of_respectsIso
    (@Space.IsSeparated B V.left.obj V.left.property) _ _).2
    (Space.isSeparated_smallerBaseInverse_map B V.left.obj S V.left.property hS V.hom _
      d.isAlgebraicSpace_eqz d.isSeparated_toBase)

/-- **The formal algebraic space of the triple of Stacks 0GHD (4) is separated over `V`**: its
structure morphism is a monomorphism, because `E_W ⟶ V` is one, so its relative diagonal is an
isomorphism. No separatedness of `X'` or `W` is used. -/
theorem isSeparatedMorphism_terminal_from_W (hVN : IsLocallyNoetherian V.left.obj) :
    FormalSpace.IsSeparatedMorphism B V.left.obj V.left.property
      (terminal.from (d.situation hVN).W) := by
  let Φ := FormalSpace.smallerBaseSheafFunctor B V.left.obj S V.left.property hS V.hom
  have hstr : Mono (FormalSpace.smallerBaseStr B V.left.obj S V.left.property hS V.hom
      (d.situation hVN).W) := by
    rw [d.situation_W hVN, ← FormalSpace.smallerBaseSheafOfIso_hom_comp]
    have : Mono d.EWToTarget := by
      unfold EWToTarget
      refine @mono_comp _ _ _ _ _ _ d.mono_EWToBase _ ?_
      exact (sheafToPresheaf _ _).mono_of_mono_map
        (show Mono (Space.sheafifiedULiftIso B S hS (yoneda.obj V)
          (isAlgebraicSpace_yoneda B S hS V).isSheaf).inv from inferInstance)
    infer_instance
  have : Mono (Φ.map (terminal.from (d.situation hVN).W)) := by
    rw [← FormalSpace.smallerBaseSheafFunctor_map_comp_str B V.left.obj S V.left.property hS
      V.hom (terminal.from (d.situation hVN).W)] at hstr
    exact mono_of_mono _ (FormalSpace.smallerBaseStr B V.left.obj S V.left.property hS V.hom _)
  have : Mono (terminal.from (d.situation hVN).W) := Φ.mono_of_mono_map this
  exact FormalSpace.isClosedImmersion_of_isIso B V.left.obj V.left.property _

/-- **A limit preserving algebraic space representing the diagonal fibre is a scheme.** For the
data of Stacks 0GHD over a locally Noetherian scheme `V`, let `E` be a limit preserving algebraic
space over `V` representing `F ×_{Δ, F × F} V` on the locally Noetherian schemes over `V`. The
values of `E` on locally Noetherian schemes are subsingletons, hence so are all its values
(`AlgebraicGeometry.ExtendingFunctors.subsingleton_obj_of_subsingleton_restriction`), so `E ⟶ V`
is a monomorphism; it is locally of finite presentation (Stacks 05N0), hence separated and locally
quasi-finite (Stacks 0463), hence representable (Stacks 0418). The result is a morphism of schemes
`e : b ⟶ V`, locally of finite type, through which morphisms factor in at most one way, and
through which a morphism `φ : A ⟶ V` from a locally Noetherian scheme factors exactly when the two
triples restrict to the same element of `F(A)`. -/
theorem exists_factors_iff_of_limitPreserving (hVN : IsLocallyNoetherian V.left.obj)
    {E : (BigFppfOver B V.left.obj V.left.property)ᵒᵖ ⥤ Type u}
    (hE : IsAlgebraicSpace B V.left.obj V.left.property E)
    (hl : LimitPreserving.{u, u, u, u, u + 1, u}
      (BigFppfOver.toScheme B V.left.obj V.left.property) E)
    (α : morOnLocallyNoetherian B V.left.obj V.left.property E ≅ d.diagonalFibre) :
    ∃ (b : BigFppfOver B S hS) (e : b ⟶ V),
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map e) ∧
      (∀ (A : BigFppfOver B S hS) (ψ ψ' : A ⟶ b), ψ ≫ e = ψ' ≫ e → ψ = ψ') ∧
      ∀ (A : BigFppfOver B S hS), IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj A) →
        ∀ φ : A ⟶ V, (∃ ψ : A ⟶ b, ψ ≫ e = φ) ↔ mapTriple c φ d.t₁ = mapTriple c φ d.t₂ := by
  have : IsLocallyNoetherian V.left.obj := hVN
  have hsubLN : ∀ W : LocallyNoetherianOver B V.left.obj V.left.property,
      Subsingleton (E.obj (op ((LocallyNoetherianOver.toBigFppfOver B V.left.obj
        V.left.property).obj W))) := by
    intro W
    refine ⟨fun x y => ?_⟩
    have h := @Subsingleton.elim _ (d.subsingleton_diagonalFibreObj W.obj)
      (α.hom.app (op W) ⟨x⟩) (α.hom.app (op W) ⟨y⟩)
    exact congrArg ULift.down (((isIso_iff_bijective (α.hom.app (op W))).1 inferInstance).1 h)
  have hsub : ∀ T, Subsingleton (E.obj (op T)) :=
    ExtendingFunctors.subsingleton_obj_of_subsingleton_restriction B V.left.property
      (ExtendingFunctors.isCoveringSheafOnSubcategory_of_isSheaf B V.left.property hE.isSheaf) hl
      hsubLN
  have hmono : Mono (terminal.from E) := by
    rw [NatTrans.mono_iff_mono_app]
    intro T
    rw [mono_iff_injective]
    intro x y _
    exact (hsub T.unop).elim x y
  have hlft := Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B V.left.obj
    V.left.property (Space.isLocallyOfFinitePresentation_of_limitPreserving B V.left.obj
      V.left.property hE hl)
  obtain ⟨hsep, hlqf⟩ := Space.isSeparated_isLocallyQuasiFinite_of_isLocallyOfFiniteType_mono B
    V.left.obj V.left.property (terminal.from E) ⟨hlft, hmono⟩
  have hrep := Space.relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B V.left.obj
    V.left.property (terminal.from E) hE (Space.isAlgebraicSpace_terminal B V.left.obj
      V.left.property) hlqf hsep
  let T₀ : BigFppfOver B V.left.obj V.left.property := Over.mk (𝟙 (B.obj V.left.property))
  have hT₀ : IsTerminal (yoneda.obj T₀) := Over.mkIdTerminal.isTerminalObj yoneda _
  have : IsIso (terminal.from (yoneda.obj T₀)) :=
    isIso_of_isTerminal hT₀ terminalIsTerminal _
  obtain ⟨b', snd, fst, hpb⟩ := hrep (terminal.from (yoneda.obj T₀))
  have : IsIso fst := hpb.isIso_fst_of_isIso
  have hsndlft : LocallyOfFiniteType
      ((BigFppfOver.toScheme B V.left.obj V.left.property).map snd) := by
    rw [← Space.isLocallyOfFiniteType_yoneda_map_iff]
    refine Space.isLocallyOfFiniteType_of_arrowIso B V.left.obj V.left.property (terminal.from E)
      (yoneda.map snd) (inv fst) (inv (terminal.from (yoneda.obj T₀))) ?_ hlft
    rw [IsIso.inv_comp_eq, ← Category.assoc, hpb.w, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  refine ⟨(Over.map V.hom).obj b', toV b', ?_, ?_, ?_⟩
  · have h : snd.left = b'.hom := (Category.comp_id _).symm.trans (Over.w snd)
    show LocallyOfFiniteType (B.inclusion.map b'.hom)
    rw [← h]
    exact hsndlft
  · intro A ψ ψ' hψ
    let φ := ψ ≫ toV b'
    let ψV : Over.mk φ.left ⟶ b' := Over.homMk ψ.left rfl
    have hψ' : ψ'.left ≫ b'.hom = φ.left := by
      have := (congrArg CommaMorphism.left hψ).symm
      simpa [φ] using this
    let ψV' : Over.mk φ.left ⟶ b' := Over.homMk ψ'.left hψ'
    have hinj : Function.Injective (fst.app (op (Over.mk φ.left))) :=
      ((isIso_iff_bijective _).1 inferInstance).1
    have h : ψV = ψV' := hinj ((hsub _).elim _ _)
    have h' : ψV.left = ψV'.left := congrArg CommaMorphism.left h
    exact Over.OverMorphism.ext h'
  · intro A hA φ
    rw [d.mapTriple_eq_iff_toV φ]
    let A' : LocallyNoetherianOver B V.left.obj V.left.property := ⟨Over.mk φ.left, hA⟩
    constructor
    · rintro ⟨ψ, hψ⟩
      let ψ' : Over.mk φ.left ⟶ b' :=
        Over.homMk ψ.left (by simpa using congrArg CommaMorphism.left hψ)
      let y := α.hom.app (op A') ⟨fst.app (op A'.obj) ψ'⟩
      exact y.2.1.symm.trans y.2.2
    · intro h
      let y : d.diagonalFibre.obj (op A') := ⟨mapTriple c (toV _) d.t₁, rfl, h⟩
      let ψ' : Over.mk φ.left ⟶ b' := (inv fst).app (op A'.obj) (α.inv.app (op A') y).down
      refine ⟨Over.homMk ψ'.left ?_, Over.OverMorphism.ext ?_⟩
      · have := Over.w ψ'
        simp only [Over.mk_hom] at this
        simp [← Category.assoc, this, Over.w φ]
      · simp

end Artin.ContractionEqualizer

namespace Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)

/-- **The bootstrap for the diagonal, over affine test objects of finite presentation.** In the
situation of Stacks 0GH8, with no separatedness of `X'` or `W`, suppose that the local rings of `S`
at its finite type points are G-rings and that every situation of Stacks 0GH8 over a base whose
local rings at finite type points are G-rings, with `X'` and `W` separated over the base, has a
limit preserving solution whose open part is the complement of `T` (Artin's theorem, Stacks 0GIB,
in the separated case). Then the equalizer of two elements of `F(V)`, for `V` affine and of finite
presentation over `S`, is representable. Indeed `V` is locally Noetherian with G-rings at its
finite type points (`AlgebraicGeometry.isGRing_stalk_of_locallyOfFiniteType`); the triple of
Stacks 0GHD (4) is a situation over `V` separated over `V`
(`AlgebraicGeometry.Artin.ContractionEqualizer.isSeparated_terminal_from`,
`AlgebraicGeometry.Artin.ContractionEqualizer.isSeparatedMorphism_terminal_from_W`); its solution
represents `F ×_{Δ, F × F} V` (Stacks 0GHD, final conclusion) and is a scheme
(`AlgebraicGeometry.Artin.ContractionEqualizer.exists_factors_iff_of_limitPreserving`). -/
theorem diagRepresentableOnAffineLfp_contractionFunctor
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s))
    (hsol : ∀ {V : Scheme.{u}} {hV : B.Contains V} (c' : ContractionSituation B V hV),
      (∀ v : V, IsFiniteTypePoint v → IsGRing (V.presheaf.stalk v)) →
      Space.IsSeparated B V hV (terminal.from c'.X') →
      FormalSpace.IsSeparatedMorphism B V hV (terminal.from c'.W) →
      ∃ (E : (BigFppfOver B V hV)ᵒᵖ ⥤ Type u) (s : Solution c' E),
        Set.range (Space.pointsMap B V hV s.U.toFunctor s.U.ι) = s.Tᶜ ∧
        LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B V hV) E) :
    ExtendingFunctors.DiagRepresentableOnAffineLfp.{0} B hS (contractionFunctor c) := by
  intro V hV hVl a b
  let d : ContractionEqualizer c V.obj := ⟨a, b, a.compatible.some, b.compatible.some⟩
  have hVN : IsLocallyNoetherian V.obj.left.obj := V.property
  have : LocallyOfFiniteType (B.inclusion.map V.obj.hom) := by
    have : LocallyOfFinitePresentation (B.inclusion.map V.obj.hom) := hVl
    infer_instance
  obtain ⟨E, s, hU, hl⟩ := hsol (d.situation hVN)
    (fun v hv => isGRing_stalk_of_locallyOfFiniteType (B.inclusion.map V.obj.hom) hG v hv)
    (d.isSeparated_terminal_from hVN) (d.isSeparatedMorphism_terminal_from_W hVN)
  obtain ⟨b', e, hlft, huniq, hfac⟩ :=
    d.exists_factors_iff_of_limitPreserving hVN s.isAlgebraicSpace_X hl
      (d.morIsoDiagonalFibre hVN s hU)
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V.obj) := V.property
  have hb' : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj b') :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map e)
  refine ⟨⟨b', hb'⟩, ObjectProperty.homMk e, fun Z ψ ψ' h =>
    ObjectProperty.hom_ext _ (huniq _ _ _ (congrArg (fun k => k.hom) h)), fun Z φ => ?_⟩
  show mapTriple c φ.hom a = mapTriple c φ.hom b ↔ _
  rw [← hfac Z.obj Z.property φ.hom]
  exact ⟨fun ⟨ψ, hψ⟩ => ⟨ObjectProperty.homMk ψ, ObjectProperty.hom_ext _ hψ⟩,
    fun ⟨ψ, hψ⟩ => ⟨ψ.hom, congrArg (fun k => k.hom) hψ⟩⟩

/-- **The bootstrap for the diagonal** (Remark Stacks 0GIC, first use of separatedness). In the
situation of Stacks 0GH8, with no separatedness of `X'` or `W`, suppose that the local rings of `S`
at its finite type points are G-rings, that Artin's functor `F` is limit preserving (Stacks 0GI5),
and that Artin's theorem holds in the separated case as in
`AlgebraicGeometry.Artin.ContractionSituation.diagRepresentableOnAffineLfp_contractionFunctor`.
Then the diagonal `Δ : F ⟶ F × F` is representable: over the affine test objects of finite
presentation this is
`AlgebraicGeometry.Artin.ContractionSituation.diagRepresentableOnAffineLfp_contractionFunctor`,
and `F` is an étale sheaf (Stacks 0GHG), so Stacks 0GE5 (3) ⇒ (2) applies
(`AlgebraicGeometry.ExtendingFunctors.relativelyRepresentable_diag_of_affineLfp_of_isSheaf`). -/
theorem relativelyRepresentable_diag_contractionFunctor_of_solutions
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s))
    (hsol : ∀ {V : Scheme.{u}} {hV : B.Contains V} (c' : ContractionSituation B V hV),
      (∀ v : V, IsFiniteTypePoint v → IsGRing (V.presheaf.stalk v)) →
      Space.IsSeparated B V hV (terminal.from c'.X') →
      FormalSpace.IsSeparatedMorphism B V hV (terminal.from c'.W) →
      ∃ (E : (BigFppfOver B V hV)ᵒᵖ ⥤ Type u) (s : Solution c' E),
        Set.range (Space.pointsMap B V hV s.U.toFunctor s.U.ι) = s.Tᶜ ∧
        LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B V hV) E)
    (hlim : LimitPreserving.{u, u + 1, u, u, u + 1, u}
      (LocallyNoetherianOver.toScheme B S hS) (contractionFunctor c)) :
    (uliftYoneda.{u + 1} (C := LocallyNoetherianOver B S hS)).relativelyRepresentable
      (diag (contractionFunctor c)) := by
  have : IsLocallyNoetherian S := c.isLocallyNoetherian_base
  exact ExtendingFunctors.relativelyRepresentable_diag_of_affineLfp_of_isSheaf.{0} B hS
    (contractionFunctor_satisfiesEtaleSheafProperty (B := B) (S := S) (hS := hS) c) hlim
    (c.diagRepresentableOnAffineLfp_contractionFunctor hG hsol)

end Artin.ContractionSituation

end AlgebraicGeometry

end
