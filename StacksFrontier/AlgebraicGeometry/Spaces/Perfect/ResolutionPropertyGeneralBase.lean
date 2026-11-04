module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCondition2
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRepresentableIff
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.SchemeBaseSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyFiniteLocallyFreeTrace
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertySmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyStep1
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningNoetherianSmallerBase

/-!
# Stacks 0GV6 over a general base scheme

A quasi-compact, quasi-separated algebraic space `X` over an arbitrary scheme `S` of the site
has a finite filtration by closed subspaces of finite presentation, starting with a thickening of
`X` and ending with a subspace without points, each step of which admits an admissible blowing up
whose source has the resolution property (Stacks 0GV6).  The statement is reflected from the one
over `Spec ℤ` along the lower-shriek extension of Stacks 03I5 part (2).

## Main results

* `AlgebraicGeometry.Space.exists_closedFiltration_admissibleBlowups_resolutionProperty`:
  Stacks 0GV6 over an arbitrary base scheme, from the conclusion of Stacks 0GV5.
* `AlgebraicGeometry.Space.exists_relocalizeHom_iso`: a morphism of algebraic spaces into a
  lower-shriek extension is the extension of a morphism, up to an isomorphism of the source.
* `AlgebraicGeometry.Space.le_of_relocalizeSubfunctor_le`: the lower-shriek extension reflects
  inclusions of subfunctors.
* `AlgebraicGeometry.Space.isOpenSubspace_preimage_of_iso`: open subspaces transport along an
  isomorphism of presheaves.
* `AlgebraicGeometry.Space.hasResolutionProperty_of_iso`: the resolution property is invariant
  under isomorphism.

## References

* [Stacks Project, Tag 0GV6](https://stacks.math.columbia.edu/tag/0GV6)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Reflecting a morphism and its source along the lower-shriek extension -/

section Reflect

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS)

/-- **A morphism of presheaves into a lower-shriek extension is the extension of a morphism.**
The source is the extension of a presheaf on the big fppf site of `T`, by an isomorphism
carrying the given morphism to the extension of a morphism of presheaves there. -/
theorem exists_relocalize_map_iso {G : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u}
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : Q ⟶ (OverShriek.relocalizePresheafFunctor g).obj G) :
    ∃ (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u)
      (e : (OverShriek.relocalizePresheafFunctor g).obj F ≅ Q) (q : F ⟶ G),
      e.hom ≫ p = (OverShriek.relocalizePresheafFunctor g).map q := by
  set E := smallerBasePresheafEquivalence B T S hT hS g
  set Φ := smallerBasePresheafForgetIso B T S hT hS g
  set Qπ : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    Over.mk (p ≫ OverShriek.viewStructureMap g G)
  set c := E.counitIso.app Qπ
  refine ⟨E.inverse.obj Qπ,
    (Φ.app (E.inverse.obj Qπ)).symm ≪≫ (Over.forget (yoneda.obj (Over.mk g))).mapIso c, ?_⟩
  have hw : (p ≫ Φ.inv.app G) ≫ (E.functor.obj G).hom =
      p ≫ OverShriek.viewStructureMap g G := by
    rw [Category.assoc]
    exact congrArg (fun z => p ≫ z)
      (smallerBasePresheafForgetIso_inv_app_comp_hom B hT hS g G)
  set φ : Qπ ⟶ E.functor.obj G := Over.homMk (p ≫ Φ.inv.app G) hw with hφ
  refine ⟨E.functor.preimage (c.hom ≫ φ), ?_⟩
  have hnat := Φ.hom.naturality (E.functor.preimage (c.hom ≫ φ))
  rw [Functor.comp_map, E.functor.map_preimage] at hnat
  have key : (Over.forget (yoneda.obj (Over.mk g))).map c.hom ≫ p =
      Φ.hom.app (E.inverse.obj Qπ) ≫
        (OverShriek.relocalizePresheafFunctor g).map (E.functor.preimage (c.hom ≫ φ)) := by
    rw [← hnat]
    simp [hφ]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [key]
  simp

/-- **A morphism of algebraic spaces into a lower-shriek extension is the extension of a
morphism**, Stacks 04SG with algebraicity: the source is the extension of an algebraic space
over `T`, and the morphism the extension of a morphism over `T`, up to an isomorphism of the
source. -/
theorem exists_relocalizeHom_iso {A : AlgebraicSpaces B T hT} {Y : AlgebraicSpaces B S hS}
    (p : Y ⟶ relocalizeSpace B hT hS g A) :
    ∃ (Y₀ : AlgebraicSpaces B T hT) (e : relocalizeSpace B hT hS g Y₀ ≅ Y) (q : Y₀ ⟶ A),
      e.hom ≫ p = relocalizeHom B hT hS g q := by
  obtain ⟨F, e, q, he⟩ := exists_relocalize_map_iso B hT hS g p.hom
  have hF : IsAlgebraicSpace B T hT F :=
    (isAlgebraicSpace_viewOver_iff B T S hT hS g F).1
      (isAlgebraicSpace_of_iso B S hS e.symm Y.2)
  exact ⟨⟨F, hF⟩, ObjectProperty.isoMk _ e, ObjectProperty.homMk q,
    ObjectProperty.hom_ext _ he⟩

/-- **The subfunctor of `Λ X` cut out by a subfunctor of `X` reflects inclusions.** -/
theorem le_of_relocalizeSubfunctor_le {X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u}
    {Z Z₂ : Subfunctor X}
    (h : relocalizeSubfunctor B hT hS g Z ≤ relocalizeSubfunctor B hT hS g Z₂) : Z ≤ Z₂ := by
  intro W s hs
  have hx : (⟨⟨W.unop.hom, s⟩, rfl⟩ :
      ((OverShriek.relocalizePresheafFunctor g).obj X).obj (op (Over.mk (W.unop.hom ≫ g)))) ∈
      (relocalizeSubfunctor B hT hS g Z).obj (op (Over.mk (W.unop.hom ≫ g))) :=
    (mem_relocalizeSubfunctor_iff B hT hS g Z _ _).2 hs
  exact (mem_relocalizeSubfunctor_iff B hT hS g Z₂ _ _).1 (h _ hx)

end Reflect

/-! ### Subspaces, points and the resolution property along an isomorphism -/

section Transport

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
  {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The comparison morphism of the preimage of a subfunctor along an isomorphism is an
isomorphism.** -/
theorem isIso_fromPreimage_of_iso (ε : P ≅ Q) (V : Subfunctor Q) :
    IsIso (V.fromPreimage ε.hom) := by
  have hpb := Subfunctor.isPullback_preimage ε.hom V
  refine ⟨⟨hpb.lift (𝟙 V.toFunctor) (V.ι ≫ ε.inv) (by simp), ?_, hpb.lift_fst _ _ _⟩⟩
  refine hpb.hom_ext ?_ ?_
  · rw [Category.assoc, hpb.lift_fst, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, hpb.lift_snd, ← Category.assoc, Subfunctor.fromPreimage_ι,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]

/-- **An open subspace transports along an isomorphism of the ambient presheaf**, Stacks 02YU
part (2): the preimage of an open subspace along an isomorphism is an open subspace. -/
theorem isOpenSubspace_preimage_of_iso (ε : P ≅ Q) {V : Subfunctor Q}
    (hV : IsOpenSubspace B S hS V) : IsOpenSubspace B S hS (V.preimage ε.hom) := by
  have _ := isIso_fromPreimage_of_iso B hS ε V
  exact ⟨hV.1.of_iso (asIso (V.fromPreimage ε.hom)).symm,
    presheaf_of_isPullback B S hS (Subfunctor.isPullback_preimage ε.hom V) hV.2⟩

/-- Precomposing with an isomorphism does not change the set of points in the image of a
morphism. -/
theorem range_pointsMap_isIso_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (θ : F ≅ G)
    (k : G ⟶ H) :
    Set.range (pointsMap B S hS F (θ.hom ≫ k)) = Set.range (pointsMap B S hS G k) := by
  have hsurj : Function.Surjective (pointsMap B S hS F θ.hom) := fun y =>
    ⟨pointsMap B S hS G θ.inv y, by
      rw [← Function.comp_apply (f := pointsMap B S hS F θ.hom), ← pointsMap_comp,
        Iso.inv_hom_id, pointsMap_id, id]⟩
  rw [pointsMap_comp]
  exact hsurj.range_comp _

/-- **An isomorphism of algebraic spaces is finite locally free**, in the sense of Stacks 03ZV. -/
theorem isFiniteLocallyFree_of_isIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    [IsIso f.hom] : IsFiniteLocallyFree B S hS f := by
  have _ : MorphismProperty.RespectsIso
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.ContainsIdentities
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u}) :=
    ⟨fun W => by
      have _ := Stacks.Morphisms.isFiniteLocallyFreeOfRank_one_of_isIso (𝟙 W)
      exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (𝟙 W) 1⟩
  have _ : MorphismProperty.ContainsIdentities (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.ContainsIdentities.inverseImage _
  have _ : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  exact (isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree B S hS f).1
    (MorphismProperty.presheaf_of_isIso _ f.hom)

/-- **The resolution property of Stacks 0GUS is invariant under an isomorphism of algebraic
spaces.** -/
theorem hasResolutionProperty_of_iso {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y)
    (hX : HasResolutionProperty.{u, u} B S hS X.1 X.2) :
    HasResolutionProperty.{u, u} B S hS Y.1 Y.2 := by
  have _ : IsIso e.hom.hom :=
    ⟨⟨e.inv.hom, congrArg (fun φ : X ⟶ X => φ.hom) e.hom_inv_id,
      congrArg (fun φ : Y ⟶ Y => φ.hom) e.inv_hom_id⟩⟩
  exact hasResolutionProperty_of_isSurjective_isFiniteLocallyFree_unconditional B S hS e.hom
    (isSurjective_of_isIso B S hS e.hom.hom) (isFiniteLocallyFree_of_isIso B hS e.hom) hX

end Transport

section Points

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS)

attribute [local instance] pointTopology

/-- **The points in the image of a morphism, read over the larger base.**  The image of the
lower-shriek extension of a morphism `k` on points is the image of `k` on points, read over `S`
through `AlgebraicGeometry.Space.pointsRelocalize`. -/
theorem image_pointsRelocalize_range_pointsMap
    {F H : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u} (k : F ⟶ H) :
    pointsRelocalize B T S hT hS g H '' Set.range (pointsMap B T hT F k) =
      Set.range (pointsMap B S hS ((OverShriek.relocalizePresheafFunctor g).obj F)
        ((OverShriek.relocalizePresheafFunctor g).map k)) := by
  rw [← Set.range_comp,
    show pointsRelocalize B T S hT hS g H ∘ pointsMap B T hT F k =
        pointsMap B S hS ((OverShriek.relocalizePresheafFunctor g).obj F)
            ((OverShriek.relocalizePresheafFunctor g).map k) ∘
          pointsRelocalize B T S hT hS g F from
      funext fun x => pointsRelocalize_naturality B T S hT hS g k x]
  exact (pointsRelocalize_surjective B T S hT hS g F).range_comp _

end Points

/-! ### Stacks 0GV6 for a general base scheme -/

section GeneralBase

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **Stacks 0GV6 for an algebraic space over an arbitrary base scheme.**  For a quasi-compact,
quasi-separated algebraic space `X` over a scheme `S` of the site there are closed subspaces
`Z₀ ⊇ Z₁ ⊇ ⋯ ⊇ Z_t` of `X`, each of finite presentation over `X`, with `Z₀ ⊆ X` a thickening in
the sense of Stacks 05ZK part (1), with `Z_t` carrying no points, and with a
`(Z_i ∖ Z_{i+1})`-admissible blowing up of `Z_i` whose source has the resolution property for
every `i < t`.

The hypothesis `h0GV5` is the conclusion of Stacks 0GV5 over the terminal scheme, for every
algebraic space. -/
theorem exists_closedFiltration_admissibleBlowups_resolutionProperty
    (h0GV5 : ∀ X : AlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal,
      IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal X.1 →
      IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal X.1 →
      (irreducibleComponents (points B (⊤_ Scheme.{u}) B.contains_terminal X.1)).Finite →
      ∃ U : OpenSubspaces B (⊤_ Scheme.{u}) B.contains_terminal X.1,
        IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal U.1.toFunctor ∧
        Dense (subspacePointSet B (⊤_ Scheme.{u}) B.contains_terminal X.1 U.1) ∧
          ∃ (X' : AlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal) (b : X' ⟶ X),
            IsAdmissibleBlowup B (⊤_ Scheme.{u}) B.contains_terminal U b ∧
            HasResolutionProperty.{u, u} B (⊤_ Scheme.{u}) B.contains_terminal X'.1 X'.2)
    (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1) :
    ∃ (t : ℕ) (Z : ℕ → Subfunctor X.1) (hZ : ∀ i, IsClosedSubspace B S hS (Z i)),
      (∀ i, IsFinitePresentation B S hS (Z i).ι) ∧
      (∀ i, Z (i + 1) ≤ Z i) ∧
      IsThickening B S hS X (Z 0) ∧
      IsEmpty (points B S hS (Z t).toFunctor) ∧
      ∀ i < t, ∃ (U : OpenSubspaces B S hS (Z i).toFunctor) (Y : AlgebraicSpaces B S hS)
          (f : Y ⟶ (⟨(Z i).toFunctor, (hZ i).1⟩ : AlgebraicSpaces B S hS)),
        Set.range (pointsMap B S hS U.1.toFunctor (U.1.ι ≫ (Z i).ι)) =
            subspacePointSet B S hS X.1 (Z i) \ subspacePointSet B S hS X.1 (Z (i + 1)) ∧
          IsAdmissibleBlowup B S hS U f ∧
          HasResolutionProperty.{u, u} B S hS Y.1 Y.2 := by
  have hblowiso : ∀ (P P' Y : AlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal)
      (α : P ≅ P') (U : OpenSubspaces B (⊤_ Scheme.{u}) B.contains_terminal P.1)
      (U' : OpenSubspaces B (⊤_ Scheme.{u}) B.contains_terminal P'.1) (f : Y ⟶ P'),
      U.1 = U'.1.preimage α.hom.hom →
      IsAdmissibleBlowup B (⊤_ Scheme.{u}) B.contains_terminal U' f →
      IsAdmissibleBlowup B (⊤_ Scheme.{u}) B.contains_terminal U (f ≫ α.inv) := by
    intro P P' Y α U U' f hU h
    obtain rfl : U = ⟨U'.1.preimage α.hom.hom,
        isOpenSubspace_preimage B (⊤_ Scheme.{u}) B.contains_terminal α.hom.hom U'.1 P'.2 P.2
          U'.2⟩ := Subtype.ext hU
    exact IsAdmissibleBlowup.comp_inv α U' h
  set g : B.obj hS ⟶ B.obj B.contains_terminal := integersMap B S hS B.contains_terminal
  obtain ⟨t, Z', hZ'c, hfp', hmono', hthick', hempty', hblow'⟩ :=
    exists_closedFiltration_admissibleBlowups_resolutionProperty_overIntegers B h0GV5
      (relocalizeSpace B hS B.contains_terminal g X)
      ((isQuasiCompactSpace_relocalize_iff B S hS (⊤_ Scheme.{u}) B.contains_terminal g X.1).2
        hqc)
      ((isAbsolutelyQuasiSeparated_viewOverIntegers_iff B S hS B.contains_terminal X.1).2 hqs)
  obtain ⟨Z, rfl⟩ : ∃ Z : ℕ → Subfunctor X.1,
      Z' = fun i => relocalizeSubfunctor B hS B.contains_terminal g (Z i) :=
    ⟨fun i => OverShriek.relocalizeSubfunctorPreimage g (Z' i),
      funext fun i =>
        (OverShriek.range_map_ι_relocalizeSubfunctorPreimage g (Z' i)).symm⟩
  have hZc : ∀ i, IsClosedSubspace B S hS (Z i) := fun i =>
    (isClosedSubspace_relocalizeSubfunctor_iff B hS B.contains_terminal g (Z i)).1 (hZ'c i)
  refine ⟨t, Z, hZc, fun i =>
    (isFinitePresentation_relocalizeSubfunctor_ι_iff B hS B.contains_terminal g (Z i)).1
      (hfp' i), fun i => ?_, ?_, ?_, ?_⟩
  · exact le_of_relocalizeSubfunctor_le B hS B.contains_terminal g (hmono' i)
  · exact (isThickening_viewOverIntegers_iff B S hS B.contains_terminal X (Z 0)).1 hthick'
  · have _ := hempty'
    exact Function.isEmpty
      (fun x => pointsMap B (⊤_ Scheme.{u}) B.contains_terminal _
        (relocalizeSubfunctorIso B hS B.contains_terminal g (Z t)).hom
        (pointsRelocalize B S (⊤_ Scheme.{u}) hS B.contains_terminal g (Z t).toFunctor x))
  · intro i hi
    obtain ⟨U', Y', f', hrange', hadm', hres'⟩ := hblow' i hi
    set εp := relocalizeSubfunctorIso B hS B.contains_terminal g (Z i)
    set A : AlgebraicSpaces B S hS := ⟨(Z i).toFunctor, (hZc i).1⟩
    set α : relocalizeSpace B hS B.contains_terminal g A ≅
        (⟨(relocalizeSubfunctor B hS B.contains_terminal g (Z i)).toFunctor,
          (hZ'c i).1⟩ : AlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal) :=
      ObjectProperty.isoMk _ εp
    obtain ⟨U0, hU0⟩ : ∃ U0 : Subfunctor A.1,
        relocalizeSubfunctor B hS B.contains_terminal g U0 = U'.1.preimage εp.hom :=
      ⟨OverShriek.relocalizeSubfunctorPreimage g (U'.1.preimage εp.hom),
        OverShriek.range_map_ι_relocalizeSubfunctorPreimage g _⟩
    have hU0open : IsOpenSubspace B S hS U0 :=
      (isOpenSubspace_relocalizeSubfunctor_iff B hS B.contains_terminal g U0).1
        (by rw [hU0]; exact isOpenSubspace_preimage_of_iso B B.contains_terminal εp U'.2)
    have hadm'' : IsAdmissibleBlowup B (⊤_ Scheme.{u}) B.contains_terminal
        (openSubspacesRelocalizeEquiv B hS B.contains_terminal g A.1 ⟨U0, hU0open⟩)
        (f' ≫ α.inv) :=
      hblowiso _ _ _ α _ U' f' hU0 hadm'
    obtain ⟨Y₀, e, q, he⟩ :=
      exists_relocalizeHom_iso B hS B.contains_terminal g (f' ≫ α.inv)
    refine ⟨⟨U0, hU0open⟩, Y₀, q, ?_,
      isAdmissibleBlowup_of_viewOverIntegers_iso B S hS B.contains_terminal ⟨U0, hU0open⟩ q
        (f' ≫ α.inv) e he hadm'',
      (hasResolutionProperty_relocalize_iff B hS B.contains_terminal g Y₀.1 Y₀.2).1
        (hasResolutionProperty_of_iso B B.contains_terminal e.symm hres')⟩
    have hbij := pointsRelocalize_bijective B S (⊤_ Scheme.{u}) hS B.contains_terminal g X.1
    refine hbij.1.image_injective ?_
    simp only [subspacePointSet] at hrange' ⊢
    rw [Set.image_diff hbij.1,
      ← range_pointsMap_relocalizeSubfunctor_ι B hS B.contains_terminal g (Z i),
      ← range_pointsMap_relocalizeSubfunctor_ι B hS B.contains_terminal g (Z (i + 1)),
      ← hrange',
      image_pointsRelocalize_range_pointsMap B hS B.contains_terminal g (U0.ι ≫ (Z i).ι),
      Functor.map_comp,
      ← relocalizeSubfunctorIso_hom_ι B hS B.contains_terminal g U0,
      ← relocalizeSubfunctorIso_hom_ι B hS B.contains_terminal g (Z i)]
    simp only [Category.assoc]
    rw [range_pointsMap_isIso_comp B B.contains_terminal
        (relocalizeSubfunctorIso B hS B.contains_terminal g U0) _, hU0, ← Category.assoc,
      ← Subfunctor.fromPreimage_ι U'.1 εp.hom, Category.assoc]
    have _ := isIso_fromPreimage_of_iso B B.contains_terminal εp U'.1
    exact range_pointsMap_isIso_comp B B.contains_terminal
      (asIso (U'.1.fromPreimage εp.hom)) _

end GeneralBase

end AlgebraicGeometry.Space

end
