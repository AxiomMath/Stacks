module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelativeLimitApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.StructureMorphismBaseChange

/-!
# A small approximation by spaces of finite presentation over a base of finite presentation

Let `S` be a quasi-separated locally Noetherian scheme of a big fppf site, locally of finite
presentation over `Spec ℤ` (for instance the spectrum of a finite field). An algebraic space `X`
over `S` whose view over `Spec ℤ` has a Noetherian approximation indexed by a set small for the
site — the conclusion of Stacks 07SU with its index set bounded — is the limit of an inverse system
of algebraic spaces of finite presentation over `S` with affine transition morphisms, indexed by a
set small for the site. This is the case `Y = S` of Stacks 09NS, with the size of the index set
retained, which is what Stacks 07SR consumes.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_of_isAffineHom_relocalizeMap`: affineness of a morphism of
  presheaves descends along the lower-shriek extension of Stacks 03I5 (2).
* `AlgebraicGeometry.Space.exists_finitePresentation_system_of_hasSmallNoetherianApproximation`:
  the approximation over `S`.

## Implementation notes

The structure morphism `X_ℤ ⟶ S` is defined over a stage `a₀` of the given system, by Stacks 0CP4
(`AlgebraicGeometry.Space.exists_stage_map_of_relativelyLimitPreserving`), since `S` is locally of
finite presentation over `Spec ℤ`. The stages above `a₀` compute the same limit and are algebraic
spaces over `S`, that is, objects of the slice over the representable presheaf of `S`; the
equivalence of Stacks 04SG (`AlgebraicGeometry.smallerBasePresheafEquivalence`) returns them to the
big fppf site of `S`. Finite presentation over `S` and affineness are read off over `Spec ℤ`, where
they hold because the stages are of finite type over `Spec ℤ` and `S` is Noetherian and
quasi-separated.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 09NS](https://stacks.math.columbia.edu/tag/09NS)
* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-- **Affineness of a morphism of presheaves descends along the lower-shriek extension of
Stacks 03I5 (2).** A test of affineness of `f` over `W` extends to a test of `Λ_h f` over `S`;
the affine object representing the base change upstairs has its structure morphism to `S`
factoring through `W` by the base change square itself, so it is the image of an affine object
over `W`, and the extension reflects Cartesian squares. -/
theorem Space.isAffineHom_of_isAffineHom_relocalizeMap {F G : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G)
    (hf : Space.IsAffineHom B S hS ((OverShriek.relocalizePresheafFunctor h).map f)) :
    Space.IsAffineHom B W hW f := by
  intro Z g
  let L := OverShriek.relocalizePresheafFunctor h
  let Zi := (BigAffineFppf.inclusion B W hW).obj Z
  obtain ⟨W', p', q', hpb⟩ := hf ⟨(Over.map h).obj Zi, Z.property⟩
    (relocalizeChart B W S hW hS h g)
  obtain ⟨ψ, hψ, σ, hσ⟩ := exists_relocalizeChart B W S hW hS h _ p'
  have key : yoneda.map (relocalizeBaseHom B W S hW hS h hψ ≫
        relocalizeOverHom B W S hW hS h (Over.mk ψ)) =
      yoneda.map (q' ≫ relocalizeOverHom B W S hW hS h Zi) := by
    calc yoneda.map (relocalizeBaseHom B W S hW hS h hψ ≫
          relocalizeOverHom B W S hW hS h (Over.mk ψ))
        = p' ≫ OverShriek.relocalizeToYoneda h F := by
          rw [hσ, Category.assoc, relocalizeChart_comp_relocalizeToYoneda, yoneda.map_comp]
      _ = p' ≫ L.map f ≫ OverShriek.relocalizeToYoneda h G := by
          rw [relocalizeToYoneda_naturality]
      _ = yoneda.map q' ≫ relocalizeChart B W S hW hS h g ≫
            OverShriek.relocalizeToYoneda h G := by
          rw [← Category.assoc, hpb.w, Category.assoc]
      _ = yoneda.map (q' ≫ relocalizeOverHom B W S hW hS h Zi) := by
          rw [relocalizeChart_comp_relocalizeToYoneda, yoneda.map_comp]
  have hψ' : ψ = q'.left ≫ Zi.hom := by
    have := congrArg Over.Hom.left (yoneda.map_injective key)
    simpa [relocalizeBaseHom, relocalizeOverHom] using this
  subst hψ'
  let V : BigFppfOver B W hW := Over.mk (q'.left ≫ Zi.hom)
  let qV : V ⟶ Zi := Over.homMk q'.left rfl
  let ι := relocalizeBaseHom B W S hW hS h hψ
  have h2 : ι ≫ (Over.map h).map qV = q' := Over.OverMorphism.ext (Category.id_comp q'.left)
  have _ : ReflectsLimitsOfShape WalkingCospan L := relocalizePresheaf_reflectsPullbacks h
  have _ := relocalizePresheaf_faithful h
  let ρV := relocalizedYonedaIso B (B.obj hW) (B.obj hS) h V
  let ρZ := relocalizedYonedaIso B (B.obj hW) (B.obj hS) h Zi
  have hnat : ρV.inv ≫ L.map (yoneda.map qV) = yoneda.map ((Over.map h).map qV) ≫ ρZ.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact relocalizedYonedaIso_naturality B (B.obj hW) (B.obj hS) h qV
  have hL : IsPullback (L.map σ) (L.map (yoneda.map qV)) (L.map f) (L.map g) := by
    refine hpb.of_iso (yoneda.mapIso (asIso ι) ≪≫ ρV.symm) (Iso.refl _) ρZ.symm (Iso.refl _)
      ?_ ?_ ?_ ?_
    · change p' ≫ 𝟙 _ = (yoneda.map ι ≫ ρV.inv) ≫ L.map σ
      rw [Category.comp_id, hσ, Category.assoc]
      rfl
    · change yoneda.map q' ≫ ρZ.inv = (yoneda.map ι ≫ ρV.inv) ≫ L.map (yoneda.map qV)
      rw [Category.assoc, hnat, ← Category.assoc, ← yoneda.map_comp, h2]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · change relocalizeChart B W S hW hS h g ≫ 𝟙 _ = ρZ.inv ≫ L.map g
      rw [Category.comp_id]
      rfl
  refine ⟨⟨V, W'.property⟩, σ, qV, IsPullback.of_map L (L.map_injective ?_) hL⟩
  rw [L.map_comp, L.map_comp]
  exact hL.w

namespace Space

/-- **A small Noetherian approximation over `Spec ℤ` gives a small approximation by spaces of
finite presentation over a base of finite presentation.** Let `S` be a locally Noetherian
quasi-separated scheme of the site, locally of finite presentation over `Spec ℤ`, and `X` an
algebraic space over `S` whose view over `Spec ℤ` is the limit of an inverse system of
quasi-separated algebraic spaces of finite type over `Spec ℤ` with affine transition morphisms,
indexed by a set small for the site. Then `X` itself is the limit of an inverse system of algebraic
spaces of finite presentation over `S` with affine transition morphisms, indexed by a set small for
the site.

The structure morphism `X_ℤ ⟶ S` is defined over a stage `a₀` of the system (Stacks 0CP4, `S`
being locally of finite presentation over `Spec ℤ`), so the stages above `a₀`, which compute the
same limit, are algebraic spaces over `S`; the equivalence of Stacks 04SG returns them to the big
fppf site of `S`. -/
theorem exists_finitePresentation_system_of_hasSmallNoetherianApproximation
    (S : Scheme.{u}) (hS : B.Contains S) [QuasiSeparatedSpace S] [IsLocallyNoetherian S]
    (hSfp : LocallyOfFinitePresentation (terminal.from S))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hA : HasSmallNoetherianApproximation B (⊤_ Scheme.{u}) B.contains_terminal
      B.contains_terminal (viewOverIntegers B S hS B.contains_terminal X)) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·)),
      Cardinal.mk I < B.cutoff.ord.cof ∧
      ∃ (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (p : (Functor.const Iᵒᵖ).obj X ⟶ D),
        Nonempty (IsLimit (Cone.mk X p)) ∧
        (∀ i, IsAlgebraicSpace B S hS (D.obj i)) ∧
        (∀ i, IsFinitePresentation B S hS (toYonedaId B S hS (D.obj i))) ∧
        (∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) := by
  classical
  let hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  let g : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let L := OverShriek.relocalizePresheafFunctor g
  let YZ : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u := yoneda.obj (Over.mk g)
  let sX : L.obj X ⟶ YZ := OverShriek.relocalizeToYoneda g X
  obtain ⟨A, hAs⟩ := hA
  let := A.preorder
  let := A.nonempty
  let := A.isDirected
  -- the stages of the given approximation
  have hEft : ∀ j, IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from (A.diagram.obj j)) := fun j =>
    isFiniteType_terminal_of_isFiniteType_viewOverIntegers B hZ (A.isFiniteTypeOverIntegers j)
  have hEqc : ∀ j, IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (A.diagram.obj j) := fun j =>
    isQuasiCompactSpace_of_isFiniteType_terminal B hZ (hEft j)
  have hXZ : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (L.obj X) :=
    isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ g X hX
  have hYZ : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ YZ := isAlgebraicSpace_yoneda B _ hZ _
  have hT := isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ
  have hYZqs : IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ YZ :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B (⊤_ Scheme.{u}) hZ YZ hZ
      ⟨Over.mk g, inferInstanceAs (QuasiSeparatedSpace S), ⟨Functor.RepresentableBy.yoneda _⟩⟩
  -- the structure morphism of `S` over `Spec ℤ` is locally of finite presentation
  have hφ : IsLocallyOfFinitePresentation B (⊤_ Scheme.{u}) hZ (terminal.from YZ) := by
    let k : (Over.mk g : BigFppfOver B (⊤_ Scheme.{u}) hZ) ⟶ Over.mk (𝟙 (B.obj hZ)) :=
      Over.homMk g (by simp)
    have hterm : IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hZ)) :
        BigFppfOver B (⊤_ Scheme.{u}) hZ)) :=
      (Over.mkIdTerminal (X := B.obj hZ)).isTerminalObj yoneda _
    exact isLocallyOfFinitePresentation_of_arrowIso B (⊤_ Scheme.{u}) hZ (yoneda.map k)
      (terminal.from YZ) (𝟙 _) (hterm.uniqueUpToIso terminalIsTerminal).hom
      (terminal.hom_ext _ _)
      (isLocallyOfFinitePresentation_yoneda_map B (⊤_ Scheme.{u}) hZ k hSfp)
  have hIop : Cardinal.mk A.Iᵒᵖ < B.cutoff.ord.cof :=
    (Cardinal.mk_congr (Opposite.equivToOpposite (α := A.I))).symm.trans_lt hAs
  have hHom : ∀ a b : A.Iᵒᵖ, Cardinal.mk (a ⟶ b) < B.cutoff.ord.cof := fun a b =>
    (Cardinal.le_one_iff_subsingleton.2 inferInstance).trans_lt
      (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof)
  -- Stacks 0CP4: the structure morphism is defined over a stage
  obtain ⟨j, t, k, a, -, ht, -⟩ := exists_stage_map_of_relativelyLimitPreserving B
    (⊤_ Scheme.{u}) hZ hZ A.diagram (Cone.mk _ A.π) A.isLimit hIop hHom A.isAlgebraicSpace hEqc
    A.isAbsolutelyQuasiSeparated (fun f => A.isAffineHom_map f) hXZ hYZ hT (terminal.from YZ) hφ
    sX (Classical.arbitrary _) (terminal.from _) (terminal.hom_ext _ _)
  let a₀ : A.I := k.unop
  let t₀ : A.diagram.obj k ⟶ YZ := A.diagram.map a ≫ t
  -- the stages above `a₀`
  let I' := ↥(Set.Ici a₀)
  let : Nonempty I' := Stacks.Order.nonempty_Ici a₀
  let : IsDirected I' (· ≤ ·) := Stacks.Order.isDirected_Ici a₀
  let ι : I'ᵒᵖ ⥤ A.Iᵒᵖ := (laterStages a₀).monotone.functor.op
  have hι : ι.Initial := by
    refine Functor.initial_of_exists_of_isCofiltered _ (fun d ↦ ?_) (fun {d c} s s' ↦ ?_)
    · obtain ⟨c, hdc, hac⟩ := directed_of (· ≤ ·) d.unop a₀
      exact ⟨op ⟨c, hac⟩, ⟨(homOfLE hdc).op⟩⟩
    · exact ⟨c, 𝟙 c, Subsingleton.elim _ _⟩
  let E := ι ⋙ A.diagram
  let c' := (Cone.mk _ A.π).whisker ι
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv ι _).symm A.isLimit
  let toK : ∀ x : I'ᵒᵖ, ι.obj x ⟶ k := fun x => (homOfLE x.unop.2).op
  let t' : ∀ x : I'ᵒᵖ, E.obj x ⟶ YZ := fun x => A.diagram.map (toK x) ≫ t₀
  have ht'nat : ∀ {x y : I'ᵒᵖ} (f : x ⟶ y), E.map f ≫ t' y = t' x := by
    intro x y f
    change A.diagram.map (ι.map f) ≫ A.diagram.map (toK y) ≫ t₀ = A.diagram.map (toK x) ≫ t₀
    rw [← Category.assoc, ← A.diagram.map_comp, Subsingleton.elim (ι.map f ≫ toK y) (toK x)]
  have hcompat : ∀ x : I'ᵒᵖ, c'.π.app x ≫ t' x = sX := by
    intro x
    change A.π.app (ι.obj x) ≫ A.diagram.map (toK x) ≫ A.diagram.map a ≫ t = sX
    have hπ := A.π.naturality (toK x)
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at hπ
    rwa [← Category.assoc, ← hπ]
  -- the system as a diagram of presheaves over the representable presheaf of `S`
  let Aov : I'ᵒᵖ ⥤ Over YZ :=
    { obj := fun x => Over.mk (t' x)
      map := fun {x y} f => Over.homMk (E.map f) (ht'nat f)
      map_id := fun x => by ext1; exact E.map_id x
      map_comp := fun f f' => by ext1; exact E.map_comp f f' }
  let cOv : Cone Aov :=
    { pt := Over.mk sX
      π :=
        { app := fun x => Over.homMk (c'.π.app x) (hcompat x)
          naturality := fun x y f => by
            ext1
            exact c'.π.naturality f } }
  let : IsCofiltered I'ᵒᵖ := inferInstance
  let : CategoryTheory.IsConnected I'ᵒᵖ := IsCofiltered.isConnected I'ᵒᵖ
  let : CreatesLimitsOfShape I'ᵒᵖ (Over.forget YZ) :=
    Over.createsLimitsOfShapeForgetOfIsConnected
  have hcOv : IsLimit cOv := isLimitOfReflects (Over.forget YZ) hc'
  -- back to the big fppf site of `S` (Stacks 04SG)
  let eqv := smallerBasePresheafEquivalence B S (⊤_ Scheme.{u}) hS hZ g
  let α := smallerBasePresheafForgetIso B S (⊤_ Scheme.{u}) hS hZ g
  have hrel : ∀ F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u,
      α.hom.app F ≫ OverShriek.relocalizeToYoneda g F = (eqv.functor.obj F).hom := by
    intro F
    ext W x
    exact Over.OverMorphism.ext rfl
  let D := Aov ⋙ eqv.inverse
  have hD : IsLimit (eqv.inverse.mapCone cOv) := isLimitOfPreserves eqv.inverse hcOv
  let eFun : eqv.functor.obj X ≅ Over.mk sX := Over.isoMk (α.app X) (hrel X)
  let eX : X ≅ eqv.inverse.obj (Over.mk sX) := eqv.unitIso.app X ≪≫ eqv.inverse.mapIso eFun
  let p : (Functor.const I'ᵒᵖ).obj X ⟶ D :=
    (Functor.const I'ᵒᵖ).map eX.hom ≫ (eqv.inverse.mapCone cOv).π
  have hp : IsLimit (Cone.mk X p) :=
    IsLimit.ofIsoLimit hD (Cone.ext eX.symm (fun x => by simp [p]))
  -- the comparison of the stages with the given ones
  have hLD : ∀ x : I'ᵒᵖ, ∃ e : E.obj x ≅ L.obj (D.obj x),
      e.hom ≫ OverShriek.relocalizeToYoneda g (D.obj x) = t' x := by
    intro x
    refine ⟨((Over.forget YZ).mapIso (eqv.counitIso.app (Aov.obj x))).symm ≪≫
      α.app (D.obj x), ?_⟩
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.app_hom, Category.assoc,
      hrel]
    exact Over.w (eqv.counitIso.inv.app (Aov.obj x))
  refine ⟨I', inferInstance, inferInstance, inferInstance,
    (Cardinal.mk_subtype_le _).trans_lt hAs, D, p, ⟨hp⟩, fun x => ?_, fun x => ?_,
    fun {x y} f => ?_⟩
  · exact isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B S (⊤_ Scheme.{u}) hS hZ g
      (Aov.obj x) (A.isAlgebraicSpace _)
  · obtain ⟨e, he⟩ := hLD x
    have hlft : IsLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ (t' x) := by
      refine isLocallyOfFiniteType_of_comp B (⊤_ Scheme.{u}) hZ (A.isAlgebraicSpace _) hYZ hT
        (t' x) (terminal.from YZ) ?_
      rw [terminal.hom_ext (t' x ≫ terminal.from YZ) (terminal.from _)]
      exact (hEft _).1
    have hN : HasEtaleLocalProperty B (⊤_ Scheme.{u}) hZ YZ
        (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
      ⟨Over.mk g, 𝟙 _,
        presheaf_inverseImage_id_yoneda B _ hZ _ (fun _ hq => by have := hq; infer_instance) _,
        presheaf_inverseImage_id_yoneda B _ hZ _ (fun _ hq => by have := hq; infer_instance) _,
        inferInstanceAs (IsLocallyNoetherian S)⟩
    have hfp : IsFinitePresentation B (⊤_ Scheme.{u}) hZ (t' x) :=
      ⟨isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ
          (A.isAlgebraicSpace _) hYZ (t' x) hN hlft,
        isQuasiCompact_of_isQuasiCompactSpace B (⊤_ Scheme.{u}) hZ hZ hYZ hYZqs (hEqc _) (t' x),
        isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B (⊤_ Scheme.{u}) hZ hZ
          (A.isAlgebraicSpace _) (A.isAbsolutelyQuasiSeparated _) (t' x)⟩
    have hfp' := isFinitePresentation_of_arrowIso B (⊤_ Scheme.{u}) hZ (t' x)
      (OverShriek.relocalizeToYoneda g (D.obj x)) e.hom (𝟙 _) (by rw [he, Category.comp_id]) hfp
    exact ⟨(Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B S (⊤_ Scheme.{u}) hS hZ g _
        (D.obj x)).1 hfp'.1,
      (isQuasiCompact_relocalizeToYoneda_iff B S (⊤_ Scheme.{u}) hS hZ g (D.obj x)).1 hfp'.2.1,
      (isQuasiSeparated_relocalizeToYoneda_iff B S (⊤_ Scheme.{u}) hS hZ g (D.obj x)).1 hfp'.2.2⟩
  · apply isAffineHom_of_isAffineHom_relocalizeMap B S (⊤_ Scheme.{u}) hS hZ g
    have hL : L.map (D.map f) = α.inv.app (D.obj x) ≫
        (eqv.functor.map (eqv.inverse.map (Aov.map f))).left ≫ α.hom.app (D.obj y) :=
      (NatIso.naturality_1 α (D.map f)).symm
    rw [hL, eqv.fun_inv_map]
    simp only [Over.comp_left, Category.assoc]
    have : IsIso (eqv.counit.app (Aov.obj x)).left :=
      (Over.forget YZ).map_isIso (eqv.counit.app (Aov.obj x))
    have : IsIso (eqv.counitInv.app (Aov.obj y)).left :=
      (Over.forget YZ).map_isIso (eqv.counitInv.app (Aov.obj y))
    refine isAffineHom_iso_comp _ (isAffineHom_iso_comp _ ?_)
    rw [← Category.assoc]
    exact isAffineHom_comp_iso _ (isAffineHom_comp_iso _ (A.isAffineHom_map _))

end Space

end AlgebraicGeometry

end
