module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeAmpleFibreStage
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOpenLocusFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleStageOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId

/-!
# Stacks 0D3D from the Noetherian approximation of a proper morphism

This file assembles the proof of Stacks 0D3D. Its claim (A) over an affine scheme `U` — the
residue-field form `AlgebraicGeometry.Space.AmpleSpreadsFromResidueFieldsToOpens`, over the
integers — is proved from:

* Stacks 0A0X: `f' : X' ⟶ h_U` is the limit of a system `Xᵢ ⟶ Yᵢ` of proper morphisms of finite
  presentation between quasi-compact quasi-separated algebraic spaces of finite presentation over
  `ℤ`, with affine transition morphisms (`h0A0X`);
* Stacks 07SQ (`h07SQ`): after shrinking, the `Yᵢ` are affine schemes;
* Stacks 0D2X, part (2) (`h0D2X`): `L'` comes from an invertible module on a stage;
* Stacks 07SR (`h07SR`) and Stacks 09MT: a fibre stage `X_{i, y_i}` is a scheme on which the
  module is ample
  (`AlgebraicGeometry.Space.exists_le_isRelativelyAmple_fibre_of_isRelativelyAmple_fibre`);
* Stacks 0D3A at that stage (`h0D3A`), the stage being Noetherian, and the pullback of the open
  neighbourhood it gives (`AlgebraicGeometry.Space.exists_open_isRelativelyAmple_of_stage`);
* Stacks 0D3C, which is proved (`AlgebraicGeometry.Space.relativeAmpleFpqcDescends`).

Stacks 07SQ, 07SR and 07SF are stated under the chapter's standing convention of Section 70.2
(tag 07SD), a property of inverse systems which is not available here. The convention is
therefore an abstract property `Conv` of inverse systems of presheaves; those results are taken
as hypotheses with the convention read as `Conv`; and the two consequences of the convention the
proof needs besides — that it passes to the system of fibres (`hBC`) and that the limit of a
system of schemes satisfying it is their limit as schemes (`hSF`) — are taken as hypotheses too.
Stacks 0A0X and Stacks 0D3A are not yet proved here; Stacks 0D2X is proved, but for systems
indexed by a set below the cofinality of the site's cutoff, which a system of Stacks 0A0X need
not be, so it is taken under the convention as well. Nothing here is registered: Stacks 0D3D
will be the instantiation of
`AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_approximation`
once those inputs are theorems.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_of_isAffineHom`: a space affine over an affine space is
  affine.
* `AlgebraicGeometry.Space.isNoetherian_toScheme_of_isFinitePresentation_terminal`: an affine
  scheme of finite presentation over `ℤ` is Noetherian.
* `AlgebraicGeometry.Space.ampleSpreadsFromResidueFieldsToOpens_of_approximation`: claim (A).
* `AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_approximation`:
  the statement of Stacks 0D3D, over any base, from the inputs above.

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0A0X](https://stacks.math.columbia.edu/tag/0A0X)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 0D2X](https://stacks.math.columbia.edu/tag/0D2X)
* [Stacks Project, Tag 0D3A](https://stacks.math.columbia.edu/tag/0D3A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A space affine over an affine space is affine.** -/
theorem isAffineSpace_of_isAffineHom {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : IsAffineHom B S hS f) (hG : IsAffineSpace B S hS G) : IsAffineSpace B S hS F := by
  obtain ⟨W, hW, ⟨e⟩⟩ := hG
  obtain ⟨A, a, b, hA⟩ := hf ⟨W, hW⟩ e.inv
  have : IsIso a := hA.isIso_fst_of_isIso
  exact ⟨A.obj, A.property, ⟨(asIso a).symm⟩⟩

/-- **An affine scheme of finite presentation over `ℤ` is Noetherian.** If a presheaf `F` on
the big fppf site of `Spec ℤ` is the affine scheme `T` and its structure morphism is of finite
presentation, then `T` is a Noetherian scheme. -/
theorem isNoetherian_toScheme_of_isFinitePresentation_terminal
    {hZ : B.Contains (⊤_ Scheme.{u})} {F : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (T : BigFppfOver B (⊤_ Scheme.{u}) hZ) (hT : IsAffine ((BigFppfOver.toScheme B _ hZ).obj T))
    (e : F ≅ yoneda.obj T) (hF : IsFinitePresentation B _ hZ (terminal.from F)) :
    _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B _ hZ).obj T) := by
  let Q : MorphismProperty ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) :=
    fun _ _ f => HoldsOnEveryEtaleChart B _ hZ
      (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) f
  have : Q.RespectsIso := holdsOnEveryEtaleChart_respectsIso_presheaf B _ hZ _
  have h₂ : Q (yoneda.map (terminal.from T)) := by
    have hy : yoneda.map (terminal.from T) =
        terminal.from (yoneda.obj T) ≫ (yonedaTerminalIso B _ hZ).inv :=
      (isTerminal_yoneda_obj_terminal B _ hZ).hom_ext _ _
    rw [hy]
    exact (Q.cancel_right_of_respectsIso _ _).2
      ((holdsOnEveryEtaleChart_terminal_iff_of_iso B _ hZ _ e).1 hF.1)
  have hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B _ hZ)).presheaf (𝟙 (yoneda.obj T)) := by
    apply presheaf_id_of_iso B _ hZ
    intro V W f hf
    have : IsIso f := hf
    change AlgebraicGeometry.Etale ((BigFppfOver.toScheme B _ hZ).map f)
    infer_instance
  have : AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B _ hZ).map (terminal.from T)) :=
    prop_toScheme_map_of_holdsOnEveryEtaleChart B _ hZ h₂ (𝟙 _) hφ (Category.id_comp _).symm
  have : IsLocallyNoetherian (⊤_ Scheme.{u}) := by
    have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
    exact LocallyOfFiniteType.isLocallyNoetherian
      (terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal).hom
  have : IsLocallyNoetherian
      ((BigFppfOver.toScheme B _ hZ).obj (⊤_ (BigFppfOver B (⊤_ Scheme.{u}) hZ))) :=
    LocallyOfFiniteType.isLocallyNoetherian (toSchemeTerminalIso B _ hZ).hom
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B _ hZ).obj T) :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B _ hZ).map (terminal.from T))
  exact {}

/-- Equal morphisms of algebraic spaces have isomorphic module pullbacks. -/
private def modulePullbackCast {hZ : B.Contains (⊤_ Scheme.{u})}
    {Z W : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ} {m m' : Z ⟶ W}
    (h : m = m') (M : Modules.{u, u} B _ hZ W.1 W.2) :
    (modulePullback B _ hZ m).obj M ≅ (modulePullback B _ hZ m').obj M :=
  eqToIso (by rw [h])

/-- **Claim (A) of the proof of Stacks 0D3D, from the Noetherian approximation of `f'`.** Over the
integers, let `f' : X' ⟶ h_U` be a proper morphism to an affine scheme, `L'` an invertible
module and `u ∈ U` a point over whose residue field `L'` is ample. Then `L'` is ample over an
open neighbourhood of `u`.

The inputs are the results the source's proof cites and this development does not yet have as
theorems, each in its holder's form, with the standing convention of Section 70.2 (tag 07SD)
read as an abstract property `Conv` of inverse systems:

* `h0A0X`: Stacks 0A0X for `f'`, with the convention for the two systems it produces;
* `h07SQ`, `h07SR`: Stacks 07SQ and Stacks 07SR for situations of Stacks 084R satisfying `Conv`;
* `h07SF`: Stacks 07SF, part (1), for systems satisfying `Conv`;
* `h0D2X`: Stacks 0D2X, part (2), for situations satisfying `Conv`;
* `hBC`, `hSF`: the convention passes to the system of fibres `Xᵢ ×_{Yᵢ} h_V`, and the scheme
  the site sees as the limit of a system of schemes satisfying it is their limit as schemes;
* `h0D3A`: Stacks 0D3A at a residue field, over a Noetherian scheme of the site. -/
theorem ampleSpreadsFromResidueFieldsToOpens_of_approximation (hZ : B.Contains (⊤_ Scheme.{u}))
    (Conv : ∀ {J : Type u} [Category.{u} J],
      (J ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) → Prop)
    (h0A0X : ∀ (U : BigFppfOver B (⊤_ Scheme.{u}) hZ),
      IsAffine ((BigFppfOver.toScheme B _ hZ).obj U) →
      ∀ {X' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
        (f' : X' ⟶ representedAlgebraicSpace B _ hZ U), IsProper B _ hZ f'.hom →
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
        (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
        (eX : DX.limitCone.pt ≅ X'.1) (eY : DY.limitCone.pt ≅ yoneda.obj U),
        (∀ i : I, DX.limitCone.π.app (op i) ≫ φ.app (op i) =
          eX.hom ≫ f'.hom ≫ eY.inv ≫ DY.limitCone.π.app (op i)) ∧
        (∀ i : I, IsProper B _ hZ (φ.app (op i)) ∧ IsFinitePresentation B _ hZ (φ.app (op i))) ∧
        (∀ i : I, IsFinitePresentation B _ hZ (terminal.from (DY.system.obj (op i)))) ∧
        Conv DX.system ∧ Conv DY.system)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I), Conv D.system →
        IsAffineSpace B _ hZ D.limitCone.pt →
          ∃ i, D.base ≤ i ∧ IsAffineSpace B _ hZ (D.system.obj (op i)))
    (h07SR : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I), Conv D.system →
        D.limitCone.pt.IsRepresentable → ∃ i, (D.system.obj (op i)).IsRepresentable)
    (h07SF : ∀ {J : Type u} [Category.{u} J] [IsCofiltered J]
      (D : J ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u), Conv D →
        (∀ {i j : J} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
          ∀ i, IsAffineHom B _ hZ (limit.π D i))
    (h0D2X : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I), Conv D.system →
      ∀ (L : Modules.{u, u} B _ hZ D.limitCone.pt D.limitAlgebraicSpace),
        IsInvertibleModule ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ L →
        ∃ (i : I) (Lᵢ : Modules.{u, u} B _ hZ (D.system.obj (op i)) (D.algebraicSpace i)),
          IsInvertibleModule ⟨D.system.obj (op i), D.algebraicSpace i⟩ Lᵢ ∧
            Nonempty (L ≅ (modulePullback B _ hZ (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
              (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B _ hZ) ⟶
                ⟨D.system.obj (op i), D.algebraicSpace i⟩)).obj Lᵢ))
    (hBC : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
      (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
      (V : BigFppfOver B (⊤_ Scheme.{u}) hZ), IsAffine ((BigFppfOver.toScheme B _ hZ).obj V) →
      ∀ (k : yoneda.obj V ⟶ DY.limitCone.pt), Conv DX.system → Conv DY.system →
        Conv (constantBaseChangeSystem φ k))
    (hSF : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I), Conv D.system → ∀ i₀ : I,
        (D.system.obj (op i₀)).IsRepresentable →
        ∀ W : Over (op i₀) ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ,
          Nonempty (W ⋙ yoneda ≅ Over.forget (op i₀) ⋙ D.system) →
            PreservesLimit W (BigFppfOver.toScheme B _ hZ))
    (h0D3A : ∀ (T : BigFppfOver B (⊤_ Scheme.{u}) hZ),
      _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B _ hZ).obj T) →
      ∀ {Xᵢ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
        (fᵢ : Xᵢ ⟶ representedAlgebraicSpace B _ hZ T), IsProper B _ hZ fᵢ.hom →
      ∀ (Lᵢ : Modules.{u, u} B _ hZ Xᵢ.1 Xᵢ.2),
        Stacks.SheafOfModules.IsInvertible (structurePresheaf B _ hZ Xᵢ.1)
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B _ hZ Xᵢ.1 Xᵢ.2).O)).property Lᵢ →
      ∀ y : (BigFppfOver.toScheme B _ hZ).obj T,
        (∀ ⦃X₀ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ⦄ (p₀ : X₀ ⟶ Xᵢ)
          (f₀ : X₀ ⟶ representedAlgebraicSpace B _ hZ
            (residueFieldObject B _ hZ T y (B.residueField_spec_contains T.left.property y))),
          IsPullback p₀ f₀ fᵢ (ObjectProperty.homMk (yoneda.map
            (residueFieldMap B _ hZ T y (B.residueField_spec_contains T.left.property y)))) →
          IsRelativelyAmple B _ hZ f₀ ((modulePullback B _ hZ p₀).obj Lᵢ)) →
        ∃ V : ((BigFppfOver.toScheme B _ hZ).obj T).Opens, y ∈ V ∧
          ∀ ⦃X₁ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ⦄ (p₁ : X₁ ⟶ Xᵢ)
            (f₁ : X₁ ⟶ representedAlgebraicSpace B _ hZ (openSub T V)),
            IsPullback p₁ f₁ fᵢ (ObjectProperty.homMk (yoneda.map (openSubHom T V))) →
            IsRelativelyAmple B _ hZ f₁ ((modulePullback B _ hZ p₁).obj Lᵢ)) :
    AmpleSpreadsFromResidueFieldsToOpens B (⊤_ Scheme.{u}) hZ := by
  intro U hU X' f' hf' L' hL' u hres
  obtain ⟨I, _, _, DX, DY, φ, eX, eY, hcomm, hφ, hfpY, hconvX, hconvY⟩ := h0A0X U hU f' hf'
  have : Nonempty I := ⟨DX.base⟩
  -- the residue field of `u`
  let κ := residueFieldObject B _ hZ U u (B.residueField_spec_contains U.left.property u)
  let res : κ ⟶ U := residueFieldMap B _ hZ U u (B.residueField_spec_contains U.left.property u)
  have hκ : IsAffine ((BigFppfOver.toScheme B _ hZ).obj κ) := by
    change IsAffine (Spec (.of (U.left.1.residueField u)))
    infer_instance
  -- the limit and the stages as algebraic spaces
  let XL : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ := ⟨DX.limitCone.pt, DX.limitAlgebraicSpace⟩
  let YL : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ := ⟨DY.limitCone.pt, DY.limitAlgebraicSpace⟩
  let Xs : I → AlgebraicSpaces B (⊤_ Scheme.{u}) hZ :=
    fun i => ⟨DX.system.obj (op i), DX.algebraicSpace i⟩
  let eXa : XL ≅ X' := ObjectProperty.isoMk _ eX
  let eYa : YL ≅ representedAlgebraicSpace B _ hZ U := ObjectProperty.isoMk _ eY
  let πX : ∀ i : I, XL ⟶ Xs i := fun i => ObjectProperty.homMk (DX.limitCone.π.app (op i))
  let tX : ∀ {i j : I}, i ≤ j → (Xs j ⟶ Xs i) :=
    fun h => ObjectProperty.homMk (DX.system.map (homOfLE h).op)
  have hπt : ∀ {i j : I} (h : i ≤ j), πX j ≫ tX h = πX i := fun h => by
    ext1
    exact DX.limitCone.w (homOfLE h).op
  -- the limit morphism and the point of `Spec κ(u)`
  let fL : DX.limitCone.pt ⟶ DY.limitCone.pt := eX.hom ≫ f'.hom ≫ eY.inv
  have hfL : ∀ i : Iᵒᵖ, fL ≫ DY.limitCone.π.app i = DX.limitCone.π.app i ≫ φ.app i :=
    fun i => by
      rw [hcomm i.unop]
      simp only [fL, Category.assoc]
  let k : yoneda.obj κ ⟶ DY.limitCone.pt := yoneda.map res ≫ eY.inv
  -- Stacks 07SQ: a stage of `Y` is affine
  obtain ⟨i₁, -, hY₁⟩ := h07SQ DY hconvY ⟨U, hU, ⟨eY⟩⟩
  -- Stacks 0D2X: `L'` comes from a stage
  let Llim := (modulePullback B _ hZ eXa.hom).obj L'
  have hLlim := Stacks.SheafOfModules.isInvertible_pullbackModules_obj
      (f := smallEtaleRingedToposModulesHom B _ hZ eXa.hom) (L := L') (hL := hL')
  obtain ⟨iL, LiL, hLiL, ⟨eL⟩⟩ := h0D2X DX hconvX Llim hLlim
  have eL' : ∀ {Z : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ} (q : Z ⟶ X'),
      (modulePullback B _ hZ q).obj L' ≅
        (modulePullback B _ hZ (q ≫ eXa.inv ≫ πX iL)).obj LiL := fun {Z} q =>
    (modulePullbackCast (by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] :
          (q ≫ eXa.inv) ≫ eXa.hom = q) L').symm ≪≫
      ((modulePullbackCompIso B _ hZ (q ≫ eXa.inv) eXa.hom).app L').symm ≪≫
      (modulePullback B _ hZ (q ≫ eXa.inv)).mapIso eL ≪≫
      (modulePullbackCompIso B _ hZ (q ≫ eXa.inv) (πX iL)).app LiL ≪≫
      modulePullbackCast (Category.assoc q eXa.inv (πX iL)) LiL
  -- a common stage
  obtain ⟨i, hiL, hi₁⟩ := exists_ge_ge iL i₁
  let Li := (modulePullback B _ hZ (tX hiL)).obj LiL
  have hLi := Stacks.SheafOfModules.isInvertible_pullbackModules_obj
      (f := smallEtaleRingedToposModulesHom B _ hZ (tX hiL)) (L := LiL) (hL := hLiL)
  -- ampleness on the fibre of the limit
  have hampW : ∀ ⦃X₀ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ⦄ (p₀ : X₀ ⟶ XL)
      (f₀ : X₀ ⟶ representedAlgebraicSpace B _ hZ κ),
      IsPullback p₀ f₀ (ObjectProperty.homMk fL : XL ⟶ YL) (ObjectProperty.homMk k) →
        IsRelativelyAmple B _ hZ f₀ ((modulePullback B _ hZ (p₀ ≫ πX i)).obj Li) := by
    intro X₀ p₀ f₀ hsq
    have hsq' : IsPullback (p₀ ≫ eXa.hom) f₀ f' (ObjectProperty.homMk (yoneda.map res)) :=
      hsq.of_iso (Iso.refl _) eXa (Iso.refl _) eYa (by simp) (by simp)
        (by
          ext1
          change (eX.hom ≫ f'.hom ≫ eY.inv) ≫ eY.hom = eX.hom ≫ f'.hom
          simp)
        (by
          ext1
          change (yoneda.map res ≫ eY.inv) ≫ eY.hom = 𝟙 _ ≫ yoneda.map res
          simp)
    have heq : (p₀ ≫ eXa.hom) ≫ eXa.inv ≫ πX iL = (p₀ ≫ πX i) ≫ tX hiL := by
      rw [Category.assoc, Iso.hom_inv_id_assoc, Category.assoc, hπt]
    exact (isRelativelyAmple_congr _ (eL' (p₀ ≫ eXa.hom) ≪≫
      modulePullbackCast heq LiL ≪≫
        ((modulePullbackCompIso B _ hZ (p₀ ≫ πX i) (tX hiL)).app LiL).symm)).1
          (hres (p₀ ≫ eXa.hom) f₀ hsq')
  -- Stacks 07SR and Stacks 09MT: ampleness on a fibre stage
  obtain ⟨j, hij, hfibj⟩ := exists_le_isRelativelyAmple_fibre_of_isRelativelyAmple_fibre
    (X := DX.system) (Y := DY.system) (φ := φ) (cY := DY.limitCone) (V := κ) hZ Conv h07SR hSF
    DX.algebraicSpace DX.transition_affine DY.algebraicSpace DY.transition_affine hφ
    DX.isLimit DY.isLimit DX.limitAlgebraicSpace DY.limitAlgebraicSpace fL hfL hκ k
    (hBC DX DY φ κ hκ k hconvX hconvY) i Li hLi hampW
  -- the stage `j` of `Y` is an affine Noetherian scheme
  obtain ⟨T, hT, ⟨eT⟩⟩ := isAffineSpace_of_isAffineHom
    (DY.system.map (homOfLE (hi₁.trans hij)).op) (DY.transition_affine _) hY₁
  have hTn := isNoetherian_toScheme_of_isFinitePresentation_terminal T hT eT (hfpY j)
  let Ysj : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ := ⟨DY.system.obj (op j), DY.algebraicSpace j⟩
  let eTa : Ysj ≅ representedAlgebraicSpace B _ hZ T := ObjectProperty.isoMk _ eT
  let fj : Xs j ⟶ representedAlgebraicSpace B _ hZ T :=
    (ObjectProperty.homMk (φ.app (op j)) : Xs j ⟶ Ysj) ≫ eTa.hom
  have hfj : IsProper B _ hZ fj.hom := by
    change IsProper B _ hZ (φ.app (op j) ≫ eT.hom)
    exact isProper_comp' B _ hZ _ _ (DY.algebraicSpace j) (isAlgebraicSpace_yoneda B _ hZ T)
      (hφ j).1 (isProper_of_isIso B _ hZ _)
  let a : U ⟶ T := yoneda.preimage (eY.inv ≫ DY.limitCone.π.app (op j) ≫ eT.hom)
  let b : X' ⟶ Xs j := eXa.inv ≫ πX j
  have hw : b ≫ fj = f' ≫ ObjectProperty.homMk (yoneda.map a) := by
    ext1
    change (eX.inv ≫ DX.limitCone.π.app (op j)) ≫ φ.app (op j) ≫ eT.hom =
      f'.hom ≫ yoneda.map a
    rw [Functor.map_preimage, Category.assoc, reassoc_of% (hcomm j), Iso.inv_hom_id_assoc]
  have ha : IsAffineHom B _ hZ (yoneda.map a) :=
    isAffineHom_of_isAffineSpace B _ hZ _ (isAffineSpace_yoneda B _ hZ U hU)
      (isAffineSpace_yoneda B _ hZ T hT)
  -- Stacks 07SF: the projection from the limit is affine
  have hb : IsAffineHom B _ hZ b.hom := by
    change IsAffineHom B _ hZ (eX.inv ≫ DX.limitCone.π.app (op j))
    rw [← IsLimit.conePointUniqueUpToIso_hom_comp DX.isLimit (limit.isLimit DX.system) (op j)]
    exact isAffineHom_comp B _ hZ _ _ (isAffineHom_of_isIso _) (isAffineHom_comp B _ hZ _ _
      (isAffineHom_of_isIso _) (h07SF DX.system hconvX DX.transition_affine (op j)))
  -- the module on the stage `j`
  let Lj := (modulePullback B _ hZ (tX hij)).obj Li
  have hLj := Stacks.SheafOfModules.isInvertible_pullbackModules_obj
      (f := smallEtaleRingedToposModulesHom B _ hZ (tX hij)) (L := Li) (hL := hLi)
  have heqj : 𝟙 X' ≫ eXa.inv ≫ πX iL = (b ≫ tX hij) ≫ tX hiL := by
    simp only [b, Category.id_comp, Category.assoc, hπt]
  let e : L' ≅ (modulePullback B _ hZ b).obj Lj :=
    ((modulePullbackIdIso B _ hZ X').app L').symm ≪≫ eL' (𝟙 X') ≪≫
      modulePullbackCast heqj LiL ≪≫
      ((modulePullbackCompIso B _ hZ (b ≫ tX hij) (tX hiL)).app LiL).symm ≪≫
      ((modulePullbackCompIso B _ hZ b (tX hij)).app Li).symm
  -- ampleness on the residue-field fibre of the stage
  have hfib : ∀ ⦃X₀ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ⦄ (p₀ : X₀ ⟶ Xs j)
      (f₀ : X₀ ⟶ representedAlgebraicSpace B _ hZ κ),
      IsPullback p₀ f₀ fj (ObjectProperty.homMk (yoneda.map (res ≫ a))) →
        IsRelativelyAmple B _ hZ f₀ ((modulePullback B _ hZ p₀).obj Lj) := by
    intro X₀ p₀ f₀ hsq
    have hsq' : IsPullback p₀ f₀ (ObjectProperty.homMk (φ.app (op j)) : Xs j ⟶ Ysj)
        (ObjectProperty.homMk (k ≫ DY.limitCone.π.app (op j))) :=
      hsq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eTa.symm (by simp) (by simp)
        (by simp [fj])
        (by
          ext1
          change yoneda.map (res ≫ a) ≫ eT.inv =
            𝟙 _ ≫ (yoneda.map res ≫ eY.inv) ≫ DY.limitCone.π.app (op j)
          rw [Functor.map_comp, Functor.map_preimage]
          simp)
    exact (isRelativelyAmple_congr _ ((modulePullbackCompIso B _ hZ p₀ (tX hij)).app Li)).2
      (hfibj p₀ f₀ hsq')
  -- Stacks 0D3A at the stage, and the preimage of its open
  exact exists_open_isRelativelyAmple_of_stage (relativeAmpleFpqcDescends B _ hZ) hw ha hb Lj hLj
    e u hfib (h0D3A T hTn fj hfj Lj hLj)

/-- **Stacks 0D3D, from the Noetherian approximation of a proper morphism.** Let `S` be a scheme,
`f : X ⟶ Y` a proper morphism of algebraic spaces over `S` and `L` an invertible
`𝒪_X`-module. There is an open subspace `V ⊆ Y` such that a morphism `g : Y' ⟶ Y` of algebraic
spaces factors through `V` if and only if the pullback of `L` to `X' = Y' ×_Y X` is ample on
`X'/Y'` (Stacks 0D31).

This is the full statement of Stacks 0D3D, from the inputs of
`AlgebraicGeometry.Space.ampleSpreadsFromResidueFieldsToOpens_of_approximation` (each stated
over the integers): the reduction to claim (A) over the integers is
`Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_ampleSpreadsOverIntegers`,
and its use of Stacks 0D3C is `AlgebraicGeometry.Space.relativeAmpleFpqcDescends`. It is not
registered: the inputs are results not yet proved here. -/
theorem exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_approximation
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (Conv : ∀ {J : Type u} [Category.{u} J],
      (J ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) → Prop)
    (h0A0X : ∀ (U : BigFppfOver B (⊤_ Scheme.{u}) hZ),
      IsAffine ((BigFppfOver.toScheme B _ hZ).obj U) →
      ∀ {X' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
        (f' : X' ⟶ representedAlgebraicSpace B _ hZ U), IsProper B _ hZ f'.hom →
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
        (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
        (eX : DX.limitCone.pt ≅ X'.1) (eY : DY.limitCone.pt ≅ yoneda.obj U),
        (∀ i : I, DX.limitCone.π.app (op i) ≫ φ.app (op i) =
          eX.hom ≫ f'.hom ≫ eY.inv ≫ DY.limitCone.π.app (op i)) ∧
        (∀ i : I, IsProper B _ hZ (φ.app (op i)) ∧ IsFinitePresentation B _ hZ (φ.app (op i))) ∧
        (∀ i : I, IsFinitePresentation B _ hZ (terminal.from (DY.system.obj (op i)))) ∧
        Conv DX.system ∧ Conv DY.system)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I), Conv D.system →
        IsAffineSpace B _ hZ D.limitCone.pt →
          ∃ i, D.base ≤ i ∧ IsAffineSpace B _ hZ (D.system.obj (op i)))
    (h07SR : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I), Conv D.system →
        D.limitCone.pt.IsRepresentable → ∃ i, (D.system.obj (op i)).IsRepresentable)
    (h07SF : ∀ {J : Type u} [Category.{u} J] [IsCofiltered J]
      (D : J ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u), Conv D →
        (∀ {i j : J} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
          ∀ i, IsAffineHom B _ hZ (limit.π D i))
    (h0D2X : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I), Conv D.system →
      ∀ (L : Modules.{u, u} B _ hZ D.limitCone.pt D.limitAlgebraicSpace),
        IsInvertibleModule ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ L →
        ∃ (i : I) (Lᵢ : Modules.{u, u} B _ hZ (D.system.obj (op i)) (D.algebraicSpace i)),
          IsInvertibleModule ⟨D.system.obj (op i), D.algebraicSpace i⟩ Lᵢ ∧
            Nonempty (L ≅ (modulePullback B _ hZ (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
              (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B _ hZ) ⟶
                ⟨D.system.obj (op i), D.algebraicSpace i⟩)).obj Lᵢ))
    (hBC : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
      (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
      (V : BigFppfOver B (⊤_ Scheme.{u}) hZ), IsAffine ((BigFppfOver.toScheme B _ hZ).obj V) →
      ∀ (k : yoneda.obj V ⟶ DY.limitCone.pt), Conv DX.system → Conv DY.system →
        Conv (constantBaseChangeSystem φ k))
    (hSF : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I), Conv D.system → ∀ i₀ : I,
        (D.system.obj (op i₀)).IsRepresentable →
        ∀ W : Over (op i₀) ⥤ BigFppfOver B (⊤_ Scheme.{u}) hZ,
          Nonempty (W ⋙ yoneda ≅ Over.forget (op i₀) ⋙ D.system) →
            PreservesLimit W (BigFppfOver.toScheme B _ hZ))
    (h0D3A : ∀ (T : BigFppfOver B (⊤_ Scheme.{u}) hZ),
      _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B _ hZ).obj T) →
      ∀ {Xᵢ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
        (fᵢ : Xᵢ ⟶ representedAlgebraicSpace B _ hZ T), IsProper B _ hZ fᵢ.hom →
      ∀ (Lᵢ : Modules.{u, u} B _ hZ Xᵢ.1 Xᵢ.2),
        Stacks.SheafOfModules.IsInvertible (structurePresheaf B _ hZ Xᵢ.1)
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B _ hZ Xᵢ.1 Xᵢ.2).O)).property Lᵢ →
      ∀ y : (BigFppfOver.toScheme B _ hZ).obj T,
        (∀ ⦃X₀ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ⦄ (p₀ : X₀ ⟶ Xᵢ)
          (f₀ : X₀ ⟶ representedAlgebraicSpace B _ hZ
            (residueFieldObject B _ hZ T y (B.residueField_spec_contains T.left.property y))),
          IsPullback p₀ f₀ fᵢ (ObjectProperty.homMk (yoneda.map
            (residueFieldMap B _ hZ T y (B.residueField_spec_contains T.left.property y)))) →
          IsRelativelyAmple B _ hZ f₀ ((modulePullback B _ hZ p₀).obj Lᵢ)) →
        ∃ V : ((BigFppfOver.toScheme B _ hZ).obj T).Opens, y ∈ V ∧
          ∀ ⦃X₁ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ⦄ (p₁ : X₁ ⟶ Xᵢ)
            (f₁ : X₁ ⟶ representedAlgebraicSpace B _ hZ (openSub T V)),
            IsPullback p₁ f₁ fᵢ (ObjectProperty.homMk (yoneda.map (openSubHom T V))) →
            IsRelativelyAmple B _ hZ f₁ ((modulePullback B _ hZ p₁).obj Lᵢ))
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (hf : IsProper B S hS f.hom)
    {L : Modules.{u, u} B S hS X.1 X.2}
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).property L) :
    ∃ V : Subfunctor Y.1, IsOpenSubspace B S hS V ∧
      ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (g : Y' ⟶ Y) (p : X' ⟶ X) (f' : X' ⟶ Y'),
        IsPullback p f' f g →
          ((∃ l : Y'.1 ⟶ V.toFunctor, l ≫ V.ι = g.hom) ↔
            IsRelativelyAmple B S hS f' ((modulePullback B S hS p).obj L)) :=
  exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_ampleSpreadsOverIntegers hZ
    (relativeAmpleFpqcDescends B S hS)
    (ampleSpreadsFromResidueFieldsToOpens_of_approximation hZ Conv h0A0X h07SQ h07SR h07SF h0D2X
      hBC hSF h0D3A) hf hL

end AlgebraicGeometry.Space

end
