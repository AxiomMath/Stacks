module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ZariskiReadingPullbackTensorRestrictSquare

/-!
# The monoidality chase at the base change of the Zariski reading, with the mate square

`CategoryTheory.Functor.tensor_baseChange_of_restriction_at` asks, as its eleventh square, for the
monoidality of the comparison `μ` of the inverses of the comparisons of Stacks 04M0 at `T` and
`T'`.  That comparison is the mate of `AlgebraicGeometry.Space.representedSquareFactorizationIso`
through the two equivalences, and `CategoryTheory.Functor.mate_tensor_of_counit_at` derives its
monoidality from ten squares about the data of the mate.
`CategoryTheory.Functor.tensor_baseChange_of_restriction_mate` is the chase with the eleventh
square replaced by those ten, and `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux` is
its instance at the base change of the Zariski reading along `h : T' ⟶ T`, with the data of
`AlgebraicGeometry.Space.zariskiReadingTensorSquareAux`.  Each square of the mate is then a
hypothesis of the instance, proved in its own declaration in the spelling the instance fixes, so
that no square is stated by hand.

## Main definitions

* `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the instance.
* `AlgebraicGeometry.Space.representedSquareFactorizationTopos`: the comparison of the square of
  `h` read through `AlgebraicGeometry.Space.representedReindexEquivalenceTopos`.

## Main results

* `CategoryTheory.Equivalence.functor_map_inverseTensor_comp_counit`: the comparison of the
  inverse of an equivalence with tensor products, transposed to the counit.
* `CategoryTheory.Functor.mate_tensor_of_counit_at` and
  `CategoryTheory.Functor.tensor_baseChange_of_restriction_mate`.
* `AlgebraicGeometry.Space.representedReindexPullbackIso_hom_eq`: the two identifications of the
  pullback along the reindexing of Stacks 04M0 with the functor of the comparison agree.
* `AlgebraicGeometry.Space.pullbackTensorIsoTransport_representedReindex_hom_eq`: Stacks 03EL
  for the reindexing, in the two spellings.
* `AlgebraicGeometry.Space.zariskiReadingTensorSquareMate_1` … `_11`, `_20`: twelve of the twenty
  squares of the instance.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u

namespace CategoryTheory

/-- The inverse of an equivalence carries a comparison `K` of its functor with tensor products to
a comparison, transposed to the counit. -/
theorem Equivalence.functor_map_inverseTensor_comp_counit {C D : Type*} [Category C]
    [Category D] (E : C ≌ D) (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D) (N M : D)
    (K : E.functor.obj ((TC.obj (E.inverse.obj N)).obj (E.inverse.obj M)) ≅
      (TD.obj (E.functor.obj (E.inverse.obj N))).obj (E.functor.obj (E.inverse.obj M))) :
    E.functor.map (E.inverse.mapIso ((TD.mapIso (X := N) (Y := E.functor.obj (E.inverse.obj N))
        (E.counitIso.app N).symm).app M ≪≫
      (TD.obj (E.functor.obj (E.inverse.obj N))).mapIso (X := M)
        (Y := E.functor.obj (E.inverse.obj M)) (E.counitIso.app M).symm ≪≫ K.symm) ≪≫
      (E.unitIso.app ((TC.obj (E.inverse.obj N)).obj (E.inverse.obj M))).symm).hom ≫
      K.hom ≫ ((TD.map (E.counit.app N)).app _ ≫ (TD.obj N).map (E.counit.app M)) =
    E.counit.app ((TD.obj N).obj M) := by
  have h2 : E.functor.map
      (E.unitIso.app ((TC.obj (E.inverse.obj N)).obj (E.inverse.obj M))).symm.hom =
      E.counit.app (E.functor.obj ((TC.obj (E.inverse.obj N)).obj (E.inverse.obj M))) :=
    (E.counit_app_functor _).symm
  rw [Iso.trans_hom, Functor.map_comp, h2, Category.assoc, Functor.mapIso_hom,
    ← Category.assoc (E.functor.map (E.inverse.map _)),
    show ∀ {Y Z : D} (f : Y ⟶ Z), E.functor.map (E.inverse.map f) ≫ E.counit.app Z =
      E.counit.app Y ≫ f from fun f => E.counit.naturality f]
  simp

/-- `CategoryTheory.Functor.mate_tensor_of_counit` at one pair of objects, with every datum
occurring in the conclusion implicit, and every other datum given only at the objects where it
is used. -/
theorem Functor.mate_tensor_of_counit_at {𝒵 𝒴₁ 𝒴₂ 𝒳 : Type*} {_ : Category 𝒵}
    {_ : Category 𝒴₁} {_ : Category 𝒴₂} {_ : Category 𝒳}
    {gs : 𝒵 ⥤ 𝒴₁} {φs : 𝒴₂ ⥤ 𝒳} {G : 𝒴₂ ⥤ 𝒵} {G' : 𝒳 ⥤ 𝒴₁}
    {T𝒵 : 𝒵 ⥤ 𝒵 ⥤ 𝒵} {T₁ : 𝒴₁ ⥤ 𝒴₁ ⥤ 𝒴₁} {T₂ : 𝒴₂ ⥤ 𝒴₂ ⥤ 𝒴₂} {T𝒳 : 𝒳 ⥤ 𝒳 ⥤ 𝒳}
    {N M : 𝒴₂}
    {J : G.obj ((T₂.obj N).obj M) ⟶ (T𝒵.obj (G.obj N)).obj (G.obj M)}
    {bc : gs.obj ((T𝒵.obj (G.obj N)).obj (G.obj M)) ⟶
      (T₁.obj (gs.obj (G.obj N))).obj (gs.obj (G.obj M))}
    {μN : gs.obj (G.obj N) ⟶ G'.obj (φs.obj N)} {μM : gs.obj (G.obj M) ⟶ G'.obj (φs.obj M)}
    {μNM : gs.obj (G.obj ((T₂.obj N).obj M)) ⟶ G'.obj (φs.obj ((T₂.obj N).obj M))}
    {cφ : φs.obj ((T₂.obj N).obj M) ⟶ (T𝒳.obj (φs.obj N)).obj (φs.obj M)}
    {J' : G'.obj ((T𝒳.obj (φs.obj N)).obj (φs.obj M)) ⟶
      (T₁.obj (G'.obj (φs.obj N))).obj (G'.obj (φs.obj M))}
    (F : 𝒵 ⥤ 𝒴₂) (F' : 𝒴₁ ⥤ 𝒳) (hF' : F'.Faithful)
    (εN : F.obj (G.obj N) ⟶ N) (εM : F.obj (G.obj M) ⟶ M)
    (εNM : F.obj (G.obj ((T₂.obj N).obj M)) ⟶ (T₂.obj N).obj M)
    (ε'N : F'.obj (G'.obj (φs.obj N)) ⟶ φs.obj N) (ε'M : F'.obj (G'.obj (φs.obj M)) ⟶ φs.obj M)
    (ε'NM : F'.obj (G'.obj (φs.obj ((T₂.obj N).obj M))) ⟶ φs.obj ((T₂.obj N).obj M))
    (ε'T : F'.obj (G'.obj ((T𝒳.obj (φs.obj N)).obj (φs.obj M))) ⟶
      (T𝒳.obj (φs.obj N)).obj (φs.obj M))
    (hε'N : IsIso ε'N) (hε'M : IsIso ε'M)
    (θN : F'.obj (gs.obj (G.obj N)) ⟶ φs.obj (F.obj (G.obj N)))
    (θM : F'.obj (gs.obj (G.obj M)) ⟶ φs.obj (F.obj (G.obj M)))
    (θNM : F'.obj (gs.obj (G.obj ((T₂.obj N).obj M))) ⟶
      φs.obj (F.obj (G.obj ((T₂.obj N).obj M))))
    (θT : F'.obj (gs.obj ((T𝒵.obj (G.obj N)).obj (G.obj M))) ⟶
      φs.obj (F.obj ((T𝒵.obj (G.obj N)).obj (G.obj M))))
    (L : F.obj ((T𝒵.obj (G.obj N)).obj (G.obj M)) ⟶
      (T₂.obj (F.obj (G.obj N))).obj (F.obj (G.obj M)))
    (L'₁ : F'.obj ((T₁.obj (gs.obj (G.obj N))).obj (gs.obj (G.obj M))) ⟶
      (T𝒳.obj (F'.obj (gs.obj (G.obj N)))).obj (F'.obj (gs.obj (G.obj M))))
    (L'₂ : F'.obj ((T₁.obj (G'.obj (φs.obj N))).obj (G'.obj (φs.obj M))) ⟶
      (T𝒳.obj (F'.obj (G'.obj (φs.obj N)))).obj (F'.obj (G'.obj (φs.obj M))))
    (hL'₂ : IsIso L'₂)
    (cφ' : φs.obj ((T₂.obj (F.obj (G.obj N))).obj (F.obj (G.obj M))) ⟶
      (T𝒳.obj (φs.obj (F.obj (G.obj N)))).obj (φs.obj (F.obj (G.obj M))))
    (hε' : F'.map (G'.map cφ) ≫ ε'T = ε'NM ≫ cφ)
    (hμN : F'.map μN ≫ ε'N = θN ≫ φs.map εN) (hμM : F'.map μM ≫ ε'M = θM ≫ φs.map εM)
    (hμNM : F'.map μNM ≫ ε'NM = θNM ≫ φs.map εNM)
    (hJ : F.map J ≫ L ≫ ((T₂.map εN).app _ ≫ (T₂.obj N).map εM) = εNM)
    (hL' : F'.map ((T₁.map μN).app _ ≫ (T₁.obj _).map μM) ≫ L'₂ =
      L'₁ ≫ ((T𝒳.map (F'.map μN)).app _ ≫ (T𝒳.obj _).map (F'.map μM)))
    (hJ' : F'.map J' ≫ L'₂ ≫ ((T𝒳.map ε'N).app _ ≫ (T𝒳.obj (φs.obj N)).map ε'M) = ε'T)
    (hcφ : φs.map ((T₂.map εN).app _ ≫ (T₂.obj N).map εM) ≫ cφ =
      cφ' ≫ ((T𝒳.map (φs.map εN)).app _ ≫ (T𝒳.obj (φs.obj N)).map (φs.map εM)))
    (hRS : F'.map bc ≫ L'₁ ≫ ((T𝒳.map θN).app _ ≫ (T𝒳.obj _).map θM) =
      θT ≫ φs.map L ≫ cφ')
    (hθ : F'.map (gs.map J) ≫ θT = θNM ≫ φs.map (F.map J)) :
    gs.map J ≫ bc ≫ ((T₁.map μN).app _ ≫ (T₁.obj _).map μM) = μNM ≫ G'.map cφ ≫ J' := by
  have bm : ∀ {𝒞 𝒟 : Type _} [Category 𝒞] [Category 𝒟] (Bf : 𝒞 ⥤ 𝒞 ⥤ 𝒟) {A A' A'' X Y W : 𝒞}
      (f : A ⟶ A') (f' : A' ⟶ A'') (g : X ⟶ Y) (g' : Y ⟶ W),
      (Bf.map f).app X ≫ (Bf.obj A').map g ≫ (Bf.map f').app Y ≫ (Bf.obj A'').map g' =
        (Bf.map (f ≫ f')).app X ≫ (Bf.obj A'').map (g ≫ g') := by
    intros
    simp only [Category.assoc, Functor.map_comp, NatTrans.comp_app, NatTrans.naturality_assoc]
  have := hL'₂; have := hF'; have := hε'N; have := hε'M
  apply F'.map_injective
  rw [← cancel_mono (L'₂ ≫ ((T𝒳.map ε'N).app _ ≫ (T𝒳.obj (φs.obj N)).map ε'M))]
  have hRHS : F'.map (μNM ≫ G'.map cφ ≫ J') ≫ L'₂ ≫ ((T𝒳.map ε'N).app _ ≫
        (T𝒳.obj (φs.obj N)).map ε'M) =
      θNM ≫ φs.map εNM ≫ cφ := by
    simp only [Functor.map_comp, Category.assoc]
    rw [hJ', hε', ← Category.assoc, hμNM, Category.assoc]
  have hLHS : F'.map (gs.map J ≫ bc ≫ ((T₁.map μN).app _ ≫ (T₁.obj _).map μM)) ≫
      L'₂ ≫ ((T𝒳.map ε'N).app _ ≫ (T𝒳.obj (φs.obj N)).map ε'M) =
      θNM ≫ φs.map (F.map J ≫ L ≫ ((T₂.map εN).app _ ≫ (T₂.obj N).map εM)) ≫ cφ := by
    simp only [Functor.map_comp, Category.assoc] at hL' hRS hcφ ⊢
    rw [reassoc_of% hL', bm, hμN, hμM, ← bm, reassoc_of% hRS, ← hcφ, reassoc_of% hθ]
  rw [hLHS, hRHS, hJ]

/-- `CategoryTheory.Functor.tensor_baseChange_of_restriction_at` with the monoidality of `μ`
obtained from `CategoryTheory.Functor.mate_tensor_of_counit_at`: `μ` is the mate through two
equivalences `F ⊣ Ei`, `F' ⊣ Ei'` of a monoidal comparison `θ`. -/
theorem Functor.tensor_baseChange_of_restriction_mate
    {𝒩 𝒩' Et Et' 𝒵 𝒵' : Type*} [Category 𝒩] [Category 𝒩'] [Category Et] [Category Et']
    [i𝒵 : Category 𝒵] [i𝒵' : Category 𝒵']
    (T𝒩 : 𝒩 ⥤ 𝒩 ⥤ 𝒩) (T𝒩' : 𝒩' ⥤ 𝒩' ⥤ 𝒩') (TE : Et ⥤ Et ⥤ Et) (TE' : Et' ⥤ Et' ⥤ Et')
    (T𝒵 : 𝒵 ⥤ 𝒵 ⥤ 𝒵) (T𝒵' : 𝒵' ⥤ 𝒵' ⥤ 𝒵')
    (Ei : 𝒩 ⥤ Et) (Ei' : 𝒩' ⥤ Et') (r : Et ⥤ 𝒵) (r' : Et' ⥤ 𝒵') (R : 𝒩 ⥤ 𝒵) (R' : 𝒩' ⥤ 𝒵')
    (τs : 𝒵 ⥤ 𝒵') (gs : Et ⥤ Et') (φs : 𝒩 ⥤ 𝒩')
    (ι : ∀ X : 𝒩, r.obj (Ei.obj X) ≅ R.obj X) (ι' : ∀ X : 𝒩', r'.obj (Ei'.obj X) ≅ R'.obj X)
    (N M : 𝒩)
    (P : ∀ X : 𝒩, τs.obj (R.obj X) ⟶ R'.obj (φs.obj X))
    (μ : ∀ X : 𝒩, gs.obj (Ei.obj X) ⟶ Ei'.obj (φs.obj X))
    (cN : τs.obj (r.obj (Ei.obj N)) ⟶ r'.obj (gs.obj (Ei.obj N)))
    (cM : τs.obj (r.obj (Ei.obj M)) ⟶ r'.obj (gs.obj (Ei.obj M)))
    (cNM : τs.obj (r.obj (Ei.obj ((T𝒩.obj N).obj M))) ⟶
      r'.obj (gs.obj (Ei.obj ((T𝒩.obj N).obj M))))
    (cT : τs.obj (r.obj ((TE.obj (Ei.obj N)).obj (Ei.obj M))) ⟶
      r'.obj (gs.obj ((TE.obj (Ei.obj N)).obj (Ei.obj M))))
    (J : Ei.obj ((T𝒩.obj N).obj M) ⟶ (TE.obj (Ei.obj N)).obj (Ei.obj M))
    (K : r.obj ((TE.obj (Ei.obj N)).obj (Ei.obj M)) ⟶
      (T𝒵.obj (r.obj (Ei.obj N))).obj (r.obj (Ei.obj M)))
    (Z : R.obj ((T𝒩.obj N).obj M) ⟶ (T𝒵.obj (R.obj N)).obj (R.obj M))
    (cφ : φs.obj ((T𝒩.obj N).obj M) ⟶ (T𝒩'.obj (φs.obj N)).obj (φs.obj M))
    (J' : Ei'.obj ((T𝒩'.obj (φs.obj N)).obj (φs.obj M)) ⟶
      (TE'.obj (Ei'.obj (φs.obj N))).obj (Ei'.obj (φs.obj M)))
    (K'₁ : r'.obj ((TE'.obj (gs.obj (Ei.obj N))).obj (gs.obj (Ei.obj M))) ⟶
      (T𝒵'.obj (r'.obj (gs.obj (Ei.obj N)))).obj (r'.obj (gs.obj (Ei.obj M))))
    (K'₂ : r'.obj ((TE'.obj (Ei'.obj (φs.obj N))).obj (Ei'.obj (φs.obj M))) ⟶
      (T𝒵'.obj (r'.obj (Ei'.obj (φs.obj N)))).obj (r'.obj (Ei'.obj (φs.obj M))))
    (Z' : R'.obj ((T𝒩'.obj (φs.obj N)).obj (φs.obj M)) ⟶
      (T𝒵'.obj (R'.obj (φs.obj N))).obj (R'.obj (φs.obj M)))
    (I : ∀ X Y : 𝒵, τs.obj ((T𝒵.obj X).obj Y) ⟶ (T𝒵'.obj (τs.obj X)).obj (τs.obj Y))
    (bc : gs.obj ((TE.obj (Ei.obj N)).obj (Ei.obj M)) ⟶
      (TE'.obj (gs.obj (Ei.obj N))).obj (gs.obj (Ei.obj M)))
    (F : Et ⥤ 𝒩) (F' : Et' ⥤ 𝒩') (hF' : F'.Faithful)
    (εN : F.obj (Ei.obj N) ⟶ N) (εM : F.obj (Ei.obj M) ⟶ M)
    (εNM : F.obj (Ei.obj ((T𝒩.obj N).obj M)) ⟶ (T𝒩.obj N).obj M)
    (ε'N : F'.obj (Ei'.obj (φs.obj N)) ⟶ φs.obj N) (ε'M : F'.obj (Ei'.obj (φs.obj M)) ⟶ φs.obj M)
    (ε'NM : F'.obj (Ei'.obj (φs.obj ((T𝒩.obj N).obj M))) ⟶ φs.obj ((T𝒩.obj N).obj M))
    (ε'T : F'.obj (Ei'.obj ((T𝒩'.obj (φs.obj N)).obj (φs.obj M))) ⟶
      (T𝒩'.obj (φs.obj N)).obj (φs.obj M))
    (hε'N : IsIso ε'N) (hε'M : IsIso ε'M)
    (θN : F'.obj (gs.obj (Ei.obj N)) ⟶ φs.obj (F.obj (Ei.obj N)))
    (θM : F'.obj (gs.obj (Ei.obj M)) ⟶ φs.obj (F.obj (Ei.obj M)))
    (θNM : F'.obj (gs.obj (Ei.obj ((T𝒩.obj N).obj M))) ⟶
      φs.obj (F.obj (Ei.obj ((T𝒩.obj N).obj M))))
    (θT : F'.obj (gs.obj ((TE.obj (Ei.obj N)).obj (Ei.obj M))) ⟶
      φs.obj (F.obj ((TE.obj (Ei.obj N)).obj (Ei.obj M))))
    (L : F.obj ((TE.obj (Ei.obj N)).obj (Ei.obj M)) ⟶
      (T𝒩.obj (F.obj (Ei.obj N))).obj (F.obj (Ei.obj M)))
    (L'₁ : F'.obj ((TE'.obj (gs.obj (Ei.obj N))).obj (gs.obj (Ei.obj M))) ⟶
      (T𝒩'.obj (F'.obj (gs.obj (Ei.obj N)))).obj (F'.obj (gs.obj (Ei.obj M))))
    (L'₂ : F'.obj ((TE'.obj (Ei'.obj (φs.obj N))).obj (Ei'.obj (φs.obj M))) ⟶
      (T𝒩'.obj (F'.obj (Ei'.obj (φs.obj N)))).obj (F'.obj (Ei'.obj (φs.obj M))))
    (hL'₂ : IsIso L'₂)
    (cφ' : φs.obj ((T𝒩.obj (F.obj (Ei.obj N))).obj (F.obj (Ei.obj M))) ⟶
      (T𝒩'.obj (φs.obj (F.obj (Ei.obj N)))).obj (φs.obj (F.obj (Ei.obj M))))
    (hι' : ∀ {X Y : 𝒩'} (f : X ⟶ Y), r'.map (Ei'.map f) ≫ (ι' Y).hom = (ι' X).hom ≫ R'.map f)
    (hFN : τs.map ((ι N).hom) ≫ P N = cN ≫ r'.map (μ N) ≫ (ι' (φs.obj N)).hom)
    (hFM : τs.map ((ι M).hom) ≫ P M = cM ≫ r'.map (μ M) ≫ (ι' (φs.obj M)).hom)
    (hFNM : τs.map ((ι ((T𝒩.obj N).obj M)).hom) ≫ P ((T𝒩.obj N).obj M) =
      cNM ≫ r'.map (μ ((T𝒩.obj N).obj M)) ≫ (ι' (φs.obj ((T𝒩.obj N).obj M))).hom)
    (hZ : Z = (ι _).inv ≫ r.map J ≫ K ≫
      ((T𝒵.map ((ι N).hom)).app _ ≫ (T𝒵.obj (R.obj N)).map ((ι M).hom)))
    (hK' : r'.map ((TE'.map (μ N)).app _ ≫ (TE'.obj _).map (μ M)) ≫ K'₂ =
        K'₁ ≫ ((T𝒵'.map (r'.map (μ N))).app _ ≫ (T𝒵'.obj _).map (r'.map (μ M))))
    (hZ' : Z' = (ι' _).inv ≫ r'.map J' ≫ K'₂ ≫
      ((T𝒵'.map ((ι' (φs.obj N)).hom)).app _ ≫
        (T𝒵'.obj (R'.obj (φs.obj N))).map ((ι' (φs.obj M)).hom)))
    (hI : ∀ {X X' Y Y' : 𝒵} (f : X ⟶ X') (g : Y ⟶ Y'),
      τs.map ((T𝒵.map f).app Y ≫ (T𝒵.obj X').map g) ≫ I X' Y' =
        I X Y ≫ ((T𝒵'.map (τs.map f)).app _ ≫ (T𝒵'.obj (τs.obj X')).map (τs.map g)))
    (hZP : τs.map K ≫ I _ _ ≫ ((T𝒵'.map cN).app _ ≫ (T𝒵'.obj _).map cM) =
      cT ≫ r'.map bc ≫ K'₁)
    (hc : τs.map (r.map J) ≫ cT = cNM ≫ r'.map (gs.map J))
    (hε' : F'.map (Ei'.map cφ) ≫ ε'T = ε'NM ≫ cφ)
    (hμN : F'.map (μ N) ≫ ε'N = θN ≫ φs.map εN) (hμM : F'.map (μ M) ≫ ε'M = θM ≫ φs.map εM)
    (hμNM : F'.map (μ ((T𝒩.obj N).obj M)) ≫ ε'NM = θNM ≫ φs.map εNM)
    (hJ : F.map J ≫ L ≫ ((T𝒩.map εN).app _ ≫ (T𝒩.obj N).map εM) = εNM)
    (hL' : F'.map ((TE'.map (μ N)).app _ ≫ (TE'.obj _).map (μ M)) ≫ L'₂ =
      L'₁ ≫ ((T𝒩'.map (F'.map (μ N))).app _ ≫ (T𝒩'.obj _).map (F'.map (μ M))))
    (hJ' : F'.map J' ≫ L'₂ ≫ ((T𝒩'.map ε'N).app _ ≫ (T𝒩'.obj (φs.obj N)).map ε'M) = ε'T)
    (hcφ : φs.map ((T𝒩.map εN).app _ ≫ (T𝒩.obj N).map εM) ≫ cφ =
      cφ' ≫ ((T𝒩'.map (φs.map εN)).app _ ≫ (T𝒩'.obj (φs.obj N)).map (φs.map εM)))
    (hRS : F'.map bc ≫ L'₁ ≫ ((T𝒩'.map θN).app _ ≫ (T𝒩'.obj _).map θM) =
      θT ≫ φs.map L ≫ cφ')
    (hθ : F'.map (gs.map J) ≫ θT = θNM ≫ φs.map (F.map J)) :
    τs.map Z ≫ I (R.obj N) (R.obj M) ≫
        ((T𝒵'.map (P N)).app _ ≫ (T𝒵'.obj (R'.obj (φs.obj N))).map (P M)) =
      P ((T𝒩.obj N).obj M) ≫ R'.map cφ ≫ Z' :=
  Functor.tensor_baseChange_of_restriction_at T𝒩 T𝒩' TE TE' T𝒵 T𝒵' Ei Ei' r r' R R' τs gs φs ι ι'
    N M P μ cN cM cNM cT J K Z cφ J' K'₁ K'₂ Z' I bc hι' hFN hFM hFNM hZ hK' hZ' hI hZP hc
    (Functor.mate_tensor_of_counit_at F F' hF' εN εM εNM ε'N ε'M ε'NM ε'T hε'N hε'M θN θM θNM θT
      L L'₁ L'₂ hL'₂ cφ' hε' hμN hμM hμNM hJ hL' hJ' hcφ hRS hθ)

/-- An equation `f ≫ g = h ≫ k` transported across a change of spelling of the category, of its
objects and of the four morphisms. -/
theorem comp_eq_comp_of_heq.{v, u'} {C₁ C : Type u'} {i₁ : Category.{v} C₁} {i : Category.{v} C}
    {X₁ Y₁ Z₁ W₁ : C₁} {X Y Z W : C} {f₁ : X₁ ⟶ Y₁} {g₁ : Y₁ ⟶ Z₁} {h₁ : X₁ ⟶ W₁}
    {k₁ : W₁ ⟶ Z₁} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ W} {k : W ⟶ Z}
    (src : f₁ ≫ g₁ = h₁ ≫ k₁) (eC : C₁ = C) (ei : HEq i₁ i) (eX : HEq X₁ X) (eY : HEq Y₁ Y)
    (eZ : HEq Z₁ Z) (eW : HEq W₁ W) (hf : HEq f₁ f) (hg : HEq g₁ g) (hh : HEq h₁ h)
    (hk : HEq k₁ k) : f ≫ g = h ≫ k := by
  subst eC; cases ei; cases eX; cases eY; cases eZ; cases eW; cases hf; cases hg; cases hh
  cases hk; exact src

/-- An equation `f ≫ g = e` transported across a change of spelling of the category, of its
objects and of the three morphisms. -/
theorem comp_eq_of_heq.{v, u'} {C₁ C : Type u'} {i₁ : Category.{v} C₁} {i : Category.{v} C}
    {X₁ Y₁ Z₁ : C₁} {X Y Z : C} {f₁ : X₁ ⟶ Y₁} {g₁ : Y₁ ⟶ Z₁} {e₁ : X₁ ⟶ Z₁}
    {f : X ⟶ Y} {g : Y ⟶ Z} {e : X ⟶ Z}
    (src : f₁ ≫ g₁ = e₁) (eC : C₁ = C) (ei : HEq i₁ i) (eX : HEq X₁ X) (eY : HEq Y₁ Y)
    (eZ : HEq Z₁ Z) (hf : HEq f₁ f) (hg : HEq g₁ g) (he : HEq e₁ e) : f ≫ g = e := by
  subst eC; cases ei; cases eX; cases eY; cases eZ; cases hf; cases hg; cases he; exact src

/-- Replacing the middle factor of `f ≫ L ≫ g = e` by an equal one. -/
theorem comp_comp_eq_of_eq {C : Type*} [Category C] {X Y Z W : C} {f : X ⟶ Y} {L L' : Y ⟶ Z}
    {g : Z ⟶ W} {e : X ⟶ W} (hL : L = L') (h : f ≫ L' ≫ g = e) : f ≫ L ≫ g = e := hL ▸ h

/-- Uniqueness of left adjoints through an intermediate adjunction, with the right adjoint of the
outer two respelled. -/
theorem _root_.CategoryTheory.Adjunction.leftAdjointUniq_hom_eq_comp_of_heq {C D : Type*}
    [Category C] [Category D] {F F' F'' : C ⥤ D} {G G₁ : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (adj3 : F'' ⊣ G) (adj1' : F ⊣ G₁) (adj3' : F'' ⊣ G₁) (hG : G = G₁) (h1 : HEq adj1 adj1')
    (h3 : HEq adj3 adj3') :
    (Adjunction.leftAdjointUniq adj1' adj3').hom =
      (Adjunction.leftAdjointUniq adj1 adj2).hom ≫ (Adjunction.leftAdjointUniq adj2 adj3).hom := by
  subst hG; cases h1; cases h3; exact (Adjunction.leftAdjointUniq_trans _ _ _).symm

end CategoryTheory

namespace AlgebraicGeometry.Space

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The hypothesis number 1 of a threefold implication, as a proposition. -/
abbrev HypothesisOf₃_1 {α1 α2 α3 β : Prop} (_ : α1 → α2 → α3 → β) : Prop := α1
/-- The hypothesis number 2 of a threefold implication, as a proposition. -/
abbrev HypothesisOf₃_2 {α1 α2 α3 β : Prop} (_ : α1 → α2 → α3 → β) : Prop := α2
/-- The hypothesis number 3 of a threefold implication, as a proposition. -/
abbrev HypothesisOf₃_3 {α1 α2 α3 β : Prop} (_ : α1 → α2 → α3 → β) : Prop := α3

set_option maxHeartbeats 400000 in
-- The statement is `type_of%` of the proof term, so the term is elaborated twice in this one
-- declaration (for the statement and for the proof), which needs twice the default budget.
/-- `CategoryTheory.Adjunction.leftAdjointUniq_hom_eq_comp_of_heq` at the comparison of
Stacks 04M0, as a term whose type fixes the spelling. -/
theorem representedReindexPullbackIsoHomEqAux (U : BigFppfOver B S hS) :
    type_of% (fun hG h1 h3 =>
    Adjunction.leftAdjointUniq_hom_eq_comp_of_heq
      ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
        (Stacks.SheafOfModules.reindexRingedSiteHom (SmallEtale.topology B S hS (yoneda.obj U))
          (representedSmallEtaleEquivalence B S hS U)
          (representedSchemeCommRingStructureSheaf B S hS
            U)).toRingedToposHom.toRingedToposModulesHom).ofNatIsoRight
        (Stacks.SheafOfModules.reindexRingedSiteHom (SmallEtale.topology B S hS (yoneda.obj U))
          (representedSmallEtaleEquivalence B S hS U)
          (representedSchemeCommRingStructureSheaf B S hS U)).pushforwardModulesToposIsoGeneral)
      (Stacks.SheafOfModules.reindexRingedSiteHom (SmallEtale.topology B S hS (yoneda.obj U))
        (representedSmallEtaleEquivalence B S hS U)
        (representedSchemeCommRingStructureSheaf B S hS
          U)).toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral
      (Stacks.SheafOfModules.reindexEquivalence (J' := SmallEtale.topology B S hS (yoneda.obj U))
        (representedSmallEtaleEquivalence B S hS U)
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (representedSchemeCommRingStructureSheaf B S hS U))).toAdjunction
      ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
        (representedReindexHom B S hS U)).ofNatIsoRight (representedReindexPushforwardIso B S hS U))
      (representedReindexEquivalence B S hS U).toAdjunction hG h1 h3) :=
  fun hG h1 h3 =>
  Adjunction.leftAdjointUniq_hom_eq_comp_of_heq
    ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (Stacks.SheafOfModules.reindexRingedSiteHom (SmallEtale.topology B S hS (yoneda.obj U))
        (representedSmallEtaleEquivalence B S hS U)
        (representedSchemeCommRingStructureSheaf B S hS
          U)).toRingedToposHom.toRingedToposModulesHom).ofNatIsoRight
      (Stacks.SheafOfModules.reindexRingedSiteHom (SmallEtale.topology B S hS (yoneda.obj U))
        (representedSmallEtaleEquivalence B S hS U)
        (representedSchemeCommRingStructureSheaf B S hS U)).pushforwardModulesToposIsoGeneral)
    (Stacks.SheafOfModules.reindexRingedSiteHom (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeCommRingStructureSheaf B S hS
        U)).toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral
    (Stacks.SheafOfModules.reindexEquivalence (J' := SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (representedSchemeCommRingStructureSheaf B S hS U))).toAdjunction
    ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (representedReindexHom B S hS U)).ofNatIsoRight (representedReindexPushforwardIso B S hS U))
    (representedReindexEquivalence B S hS U).toAdjunction hG h1 h3

/-- A factor of `AlgebraicGeometry.Space.representedReindexPullbackIso_hom_eq`: the two right
adjoints. -/
theorem representedReindexPullbackIsoHomEq_1 (U : BigFppfOver B S hS) :
    HypothesisOf₃_1 (representedReindexPullbackIsoHomEqAux U) := rfl
/-- A factor of `AlgebraicGeometry.Space.representedReindexPullbackIso_hom_eq`: the first two
adjunctions. -/
theorem representedReindexPullbackIsoHomEq_2 (U : BigFppfOver B S hS) :
    HypothesisOf₃_2 (representedReindexPullbackIsoHomEqAux U) := HEq.rfl
/-- A factor of `AlgebraicGeometry.Space.representedReindexPullbackIso_hom_eq`: the last two
adjunctions. -/
theorem representedReindexPullbackIsoHomEq_3 (U : BigFppfOver B S hS) :
    HypothesisOf₃_3 (representedReindexPullbackIsoHomEqAux U) := HEq.rfl

/-- **The pullback along the reindexing of Stacks 04M0, identified with the functor of the
comparison by uniqueness of left adjoints**, is
`Stacks.SheafOfModules.pullbackModulesReindexIso`. -/
theorem representedReindexPullbackIso_hom_eq (U : BigFppfOver B S hS) :
    (representedReindexPullbackIso B S hS U).hom =
      (Stacks.SheafOfModules.pullbackModulesReindexIso (SmallEtale.topology B S hS (yoneda.obj U))
        (representedSmallEtaleEquivalence B S hS U)
        (representedSchemeCommRingStructureSheaf B S hS U)).hom :=
  representedReindexPullbackIsoHomEqAux U (representedReindexPullbackIsoHomEq_1 U)
    (representedReindexPullbackIsoHomEq_2 U) (representedReindexPullbackIsoHomEq_3 U)

/-- The pullback along the reindexing read through `representedReindexPullbackIso` and through
`pullbackModulesReindexIso`, as a term whose type fixes the spelling. -/
theorem pullbackTensorIsoTransportRepresentedReindexAux (U : BigFppfOver B S hS)
    (P Q : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) U.left.obj
          U.left.property).toRingedTopos.O)) :
    type_of% (fun (hα : (representedReindexPullbackIso B S hS U).hom =
        (Stacks.SheafOfModules.pullbackModulesReindexIso (SmallEtale.topology B S hS (yoneda.obj U))
          (representedSmallEtaleEquivalence B S hS U)
          (representedSchemeCommRingStructureSheaf B S hS U)).hom) =>
      congrArg (fun α => (Stacks.SheafOfModules.pullbackTensorIsoTransport
        (representedReindexHom B S hS U) α P Q).hom) (Iso.ext hα)) :=
  fun (hα : (representedReindexPullbackIso B S hS U).hom =
      (Stacks.SheafOfModules.pullbackModulesReindexIso (SmallEtale.topology B S hS (yoneda.obj U))
        (representedSmallEtaleEquivalence B S hS U)
        (representedSchemeCommRingStructureSheaf B S hS U)).hom) =>
    congrArg (fun α => (Stacks.SheafOfModules.pullbackTensorIsoTransport
      (representedReindexHom B S hS U) α P Q).hom) (Iso.ext hα)

/-- Stacks 03EL for the reindexing read through `representedReindexPullbackIso` is
`AlgebraicGeometry.Space.representedSmallEtaleModuleTensorIso`. -/
theorem pullbackTensorIsoTransport_representedReindex_hom_eq (U : BigFppfOver B S hS)
    (P Q : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) U.left.obj
          U.left.property).toRingedTopos.O)) :
    (Stacks.SheafOfModules.pullbackTensorIsoTransport (representedReindexHom B S hS U)
      (representedReindexPullbackIso B S hS U) P Q).hom =
    (representedSmallEtaleModuleTensorIso B S hS U P Q).hom :=
  pullbackTensorIsoTransportRepresentedReindexAux U P Q (representedReindexPullbackIso_hom_eq U)

variable {T T' : BigFppfOver B S hS} (h : T' ⟶ T)

/-- `AlgebraicGeometry.Space.representedSquareFactorizationIso` as a comparison of the
composites of the functors of `AlgebraicGeometry.Space.representedReindexEquivalenceTopos`. -/
abbrev representedSquareFactorizationTopos :
    (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
      h.left).toRingedToposSiteHom.pullbackToposGeneral ⋙
    (representedReindexEquivalenceTopos T').functor ⟶
    (representedReindexEquivalenceTopos T).functor ⋙
    (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules :=
  (representedSquareFactorizationIso B S hS h (relativelyRepresentable_yoneda_map B S hS h)).hom

/-- The hypothesis number 1 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_1
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α1
/-- The hypothesis number 2 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_2
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α2
/-- The hypothesis number 3 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_3
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α3
/-- The hypothesis number 4 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_4
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α4
/-- The hypothesis number 5 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_5
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α5
/-- The hypothesis number 6 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_6
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α6
/-- The hypothesis number 7 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_7
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α7
/-- The hypothesis number 8 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_8
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α8
/-- The hypothesis number 9 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_9
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α9
/-- The hypothesis number 10 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_10
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α10
/-- The hypothesis number 11 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_11
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α11
/-- The hypothesis number 12 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_12
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α12
/-- The hypothesis number 13 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_13
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α13
/-- The hypothesis number 14 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_14
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α14
/-- The hypothesis number 15 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_15
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α15
/-- The hypothesis number 16 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_16
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α16
/-- The hypothesis number 17 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_17
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α17
/-- The hypothesis number 18 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_18
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α18
/-- The hypothesis number 19 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_19
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α19
/-- The hypothesis number 20 of a twentyfold implication, as a proposition. -/
abbrev HypothesisOf₂₀_20
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := α20
/-- The conclusion of a twentyfold implication, as a proposition. -/
abbrev ConclusionOf₂₀
    {α1 α2 α3 α4 α5 α6 α7 α8 α9 α10 α11 α12 α13 α14 α15 α16 α17 α18 α19 α20 β : Prop}
    (_ : α1 → α2 → α3 → α4 → α5 → α6 → α7 → α8 → α9 → α10 → α11 → α12 → α13 → α14 → α15 → α16 →
      α17 → α18 → α19 → α20 → β) : Prop := β

variable (N M : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite)

/-- `CategoryTheory.Functor.tensor_baseChange_of_restriction_mate` at the data of
`AlgebraicGeometry.Space.zariskiReadingTensorSquareAux`, with the data of the mate still to be
given: a term whose type fixes the spelling. -/
theorem zariskiReadingTensorSquareMateDataAux :
    type_of% (fun F F' hF' εN εM εNM ε'N ε'M ε'NM ε'T hε'N hε'M θN θM θNM θT L L'₁ L'₂ hL'₂ cφ' =>
    Functor.tensor_baseChange_of_restriction_mate
      (𝒵 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
      (𝒵' := ((BigFppfOver.toScheme B S hS).obj T').Modules) (i𝒵 := Scheme.Modules.instCategory)
      (i𝒵' := Scheme.Modules.instCategory)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T.left.obj
          T.left.property).toRingedTopos.O)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T'.left.obj
          T'.left.property).toRingedTopos.O)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj T').zariskiRingedSite.toRingedTopos.O)
      (representedReindexEquivalenceTopos T).inverse (representedReindexEquivalenceTopos T').inverse
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property)
      (zariskiReadingFunctor T) (zariskiReadingFunctor T')
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h))
      (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        h.left).toRingedToposSiteHom.pullbackToposGeneral
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules
      (fun X => (zariskiReadingIsoTopos T).app X) (fun X => (zariskiReadingIsoTopos T').app X)
      N M (fun X => (zariskiReadingPullbackHom h).app X)
      (fun X => Adjunction.equivalenceMateApp (representedReindexEquivalenceTopos T)
        (representedReindexEquivalenceTopos T')
        (representedSquareFactorizationIso B S hS h
          (relativelyRepresentable_yoneda_map B S hS h)).hom X)
      ((zariskiReadingRestrictPullbackIso h _
        (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN))).hom
      ((zariskiReadingRestrictPullbackIso h _
        (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM))).hom
      ((zariskiReadingRestrictPullbackIso h _
        (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T _
          (isQuasicoherentOnSite_sheafTensor_yoneda N M hN hM)))).hom
      ((zariskiReadingRestrictPullbackIso h _
        (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_sheafTensor
          (associatedBigEtaleSite B) T.left.obj T.left.property _ _
          (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN)
          (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM)))).hom
      (zariskiReadingInverseTensorIso T N M).hom
      ((zariskiReadingRestrictTensorIso T N M hN hM).hom)
      (zariskiReadingTensorIso T N M hN hM).hom
      (zariskiReadingSpaceTensorIso h N M).hom
      (zariskiReadingInverseTensorIso T'
        ((smallEtaleRingedToposModulesHom B S hS
          (representedSpaceMap B S hS h)).pullbackModules.obj N)
        ((smallEtaleRingedToposModulesHom B S hS
          (representedSpaceMap B S hS h)).pullbackModules.obj M)).hom
      (zariskiReadingRestrictPullbackTensorIso h _ _
        (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN)
        (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM)).hom
      (zariskiReadingRestrictTensorIso T'
        ((smallEtaleRingedToposModulesHom B S hS
          (representedSpaceMap B S hS h)).pullbackModules.obj N)
        ((smallEtaleRingedToposModulesHom B S hS
          (representedSpaceMap B S hS h)).pullbackModules.obj M)
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) N hN)
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) M hM)).hom
      (zariskiReadingTensorIso T' _ _
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) N hN)
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) M hM)).hom
      (fun X Y => (Stacks.RingedSpace.comparisonBifunctorIso
        ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.app (X, Y))
      (zariskiReadingEtaleBaseChangeTensorIso h _ _).hom
      F F' hF' εN εM εNM ε'N ε'M ε'NM ε'T hε'N hε'M θN θM θNM θT L L'₁ L'₂ hL'₂ cφ') :=
  fun F F' hF' εN εM εNM ε'N ε'M ε'NM ε'T hε'N hε'M θN θM θNM θT L L'₁ L'₂ hL'₂ cφ' =>
  Functor.tensor_baseChange_of_restriction_mate (𝒵 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (𝒵' := ((BigFppfOver.toScheme B S hS).obj T').Modules) (i𝒵 := Scheme.Modules.instCategory)
    (i𝒵' := Scheme.Modules.instCategory)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')))
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T.left.obj
        T.left.property).toRingedTopos.O)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) T'.left.obj
        T'.left.property).toRingedTopos.O)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((BigFppfOver.toScheme B S hS).obj T').zariskiRingedSite.toRingedTopos.O)
    (representedReindexEquivalenceTopos T).inverse (representedReindexEquivalenceTopos T').inverse
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property)
    (zariskiReadingFunctor T) (zariskiReadingFunctor T')
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h))
    (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
      h.left).toRingedToposSiteHom.pullbackToposGeneral
    (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)).pullbackModules
    (fun X => (zariskiReadingIsoTopos T).app X) (fun X => (zariskiReadingIsoTopos T').app X)
    N M (fun X => (zariskiReadingPullbackHom h).app X)
    (fun X => Adjunction.equivalenceMateApp (representedReindexEquivalenceTopos T)
      (representedReindexEquivalenceTopos T')
      (representedSquareFactorizationIso B S hS h
        (relativelyRepresentable_yoneda_map B S hS h)).hom X)
    ((zariskiReadingRestrictPullbackIso h _
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN))).hom
    ((zariskiReadingRestrictPullbackIso h _
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM))).hom
    ((zariskiReadingRestrictPullbackIso h _
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T _
        (isQuasicoherentOnSite_sheafTensor_yoneda N M hN hM)))).hom
    ((zariskiReadingRestrictPullbackIso h _
      (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_sheafTensor
        (associatedBigEtaleSite B) T.left.obj T.left.property _ _
        (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN)
        (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM)))).hom
    (zariskiReadingInverseTensorIso T N M).hom
    ((zariskiReadingRestrictTensorIso T N M hN hM).hom)
    (zariskiReadingTensorIso T N M hN hM).hom
    (zariskiReadingSpaceTensorIso h N M).hom
    (zariskiReadingInverseTensorIso T'
      ((smallEtaleRingedToposModulesHom B S hS
        (representedSpaceMap B S hS h)).pullbackModules.obj N)
      ((smallEtaleRingedToposModulesHom B S hS
        (representedSpaceMap B S hS h)).pullbackModules.obj M)).hom
    (zariskiReadingRestrictPullbackTensorIso h _ _
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T N hN)
      (isQuasicoherentOnSite_representedReindexEquivalenceTopos_inverse T M hM)).hom
    (zariskiReadingRestrictTensorIso T'
      ((smallEtaleRingedToposModulesHom B S hS
        (representedSpaceMap B S hS h)).pullbackModules.obj N)
      ((smallEtaleRingedToposModulesHom B S hS
        (representedSpaceMap B S hS h)).pullbackModules.obj M)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (representedSpaceMap B S hS h) N hN)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (representedSpaceMap B S hS h) M hM)).hom
    (zariskiReadingTensorIso T' _ _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (representedSpaceMap B S hS h) N hN)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (representedSpaceMap B S hS h) M hM)).hom
    (fun X Y => (Stacks.RingedSpace.comparisonBifunctorIso
      ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.app (X, Y))
    (zariskiReadingEtaleBaseChangeTensorIso h _ _).hom
    F F' hF' εN εM εNM ε'N ε'M ε'NM ε'T hε'N hε'M θN θM θNM θT L L'₁ L'₂ hL'₂ cφ'

/-- **`CategoryTheory.Functor.tensor_baseChange_of_restriction_mate` instantiated** at the base
change of the Zariski reading along `h`: the data of
`AlgebraicGeometry.Space.zariskiReadingTensorSquareAux`, with the comparison of Stacks 04M0 of
`AlgebraicGeometry.Space.representedReindexEquivalenceTopos`, its counits,
`AlgebraicGeometry.Space.representedSquareFactorizationTopos` and Stacks 03EL for the reindexings
and for the morphism of represented spaces as the data of the mate.  A term whose type is the
implication from the twenty squares to the monoidality square. -/
theorem zariskiReadingTensorSquareMateAux :
    type_of% (zariskiReadingTensorSquareMateDataAux h N M hN hM
      (representedReindexEquivalenceTopos T).functor (representedReindexEquivalenceTopos T').functor
      inferInstance
      ((representedReindexEquivalenceTopos T).counit.app _)
      ((representedReindexEquivalenceTopos T).counit.app _)
      ((representedReindexEquivalenceTopos T).counit.app _)
      ((representedReindexEquivalenceTopos T').counit.app _)
      ((representedReindexEquivalenceTopos T').counit.app _)
      ((representedReindexEquivalenceTopos T').counit.app _)
      ((representedReindexEquivalenceTopos T').counit.app _)
      (Iso.isIso_hom ((representedReindexEquivalenceTopos T').counitIso.app _))
      (Iso.isIso_hom ((representedReindexEquivalenceTopos T').counitIso.app _))
      ((representedSquareFactorizationTopos h).app _)
      ((representedSquareFactorizationTopos h).app _)
      ((representedSquareFactorizationTopos h).app _)
      ((representedSquareFactorizationTopos h).app _)
      (Stacks.SheafOfModules.pullbackTensorIsoTransport (representedReindexHom B S hS T)
        (representedReindexPullbackIso B S hS T) _ _).hom
      (Stacks.SheafOfModules.pullbackTensorIsoTransport (representedReindexHom B S hS T')
        (representedReindexPullbackIso B S hS T') _ _).hom
      (Stacks.SheafOfModules.pullbackTensorIsoTransport (representedReindexHom B S hS T')
        (representedReindexPullbackIso B S hS T') _ _).hom
      (Iso.isIso_hom _)
      (zariskiReadingSpaceTensorIso h _ _).hom) :=
  zariskiReadingTensorSquareMateDataAux h N M hN hM
    (representedReindexEquivalenceTopos T).functor (representedReindexEquivalenceTopos T').functor
    inferInstance
    ((representedReindexEquivalenceTopos T).counit.app _)
    ((representedReindexEquivalenceTopos T).counit.app _)
    ((representedReindexEquivalenceTopos T).counit.app _)
    ((representedReindexEquivalenceTopos T').counit.app _)
    ((representedReindexEquivalenceTopos T').counit.app _)
    ((representedReindexEquivalenceTopos T').counit.app _)
    ((representedReindexEquivalenceTopos T').counit.app _)
    (Iso.isIso_hom ((representedReindexEquivalenceTopos T').counitIso.app _))
    (Iso.isIso_hom ((representedReindexEquivalenceTopos T').counitIso.app _))
    ((representedSquareFactorizationTopos h).app _)
    ((representedSquareFactorizationTopos h).app _)
    ((representedSquareFactorizationTopos h).app _)
    ((representedSquareFactorizationTopos h).app _)
    (Stacks.SheafOfModules.pullbackTensorIsoTransport (representedReindexHom B S hS T)
      (representedReindexPullbackIso B S hS T) _ _).hom
    (Stacks.SheafOfModules.pullbackTensorIsoTransport (representedReindexHom B S hS T')
      (representedReindexPullbackIso B S hS T') _ _).hom
    (Stacks.SheafOfModules.pullbackTensorIsoTransport (representedReindexHom B S hS T')
      (representedReindexPullbackIso B S hS T') _ _).hom
    (Iso.isIso_hom _)
    (zariskiReadingSpaceTensorIso h _ _).hom

/-- Hypothesis 1 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the first
square. -/
theorem zariskiReadingTensorSquareMate_1 :
    HypothesisOf₂₀_1 (zariskiReadingTensorSquareMateAux h N M hN hM) :=
  zariskiReadingTensorSquare_readingNaturality h N M hN hM

/-- Hypothesis 2 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the second
square. -/
theorem zariskiReadingTensorSquareMate_2 :
    HypothesisOf₂₀_2 (zariskiReadingTensorSquareMateAux h N M hN hM) :=
  zariskiReadingTensorSquare_baseChange_left h N M hN hM

/-- Hypothesis 3 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the third
square. -/
theorem zariskiReadingTensorSquareMate_3 :
    HypothesisOf₂₀_3 (zariskiReadingTensorSquareMateAux h N M hN hM) :=
  zariskiReadingTensorSquare_baseChange_right h N M hN hM

/-- Hypothesis 4 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the fourth
square. -/
theorem zariskiReadingTensorSquareMate_4 :
    HypothesisOf₂₀_4 (zariskiReadingTensorSquareMateAux h N M hN hM) :=
  zariskiReadingTensorSquare_baseChange_tensor h N M hN hM

/-- Hypothesis 5 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the fifth
square. -/
theorem zariskiReadingTensorSquareMate_5 :
    HypothesisOf₂₀_5 (zariskiReadingTensorSquareMateAux h N M hN hM) :=
  zariskiReadingTensorSquare_tensorIso_source h N M hN hM

/-- Hypothesis 6 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the sixth
square. -/
theorem zariskiReadingTensorSquareMate_6 :
    HypothesisOf₂₀_6 (zariskiReadingTensorSquareMateAux h N M hN hM) :=
  zariskiReadingTensorSquare_restrictTensorNaturality h N M hN hM

/-- Hypothesis 7 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the seventh
square. -/
theorem zariskiReadingTensorSquareMate_7 :
    HypothesisOf₂₀_7 (zariskiReadingTensorSquareMateAux h N M hN hM) :=
  zariskiReadingTensorSquare_tensorIso_target h N M hN hM

/-- Hypothesis 8 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the eighth
square. -/
theorem zariskiReadingTensorSquareMate_8 :
    HypothesisOf₂₀_8 (zariskiReadingTensorSquareMateAux h N M hN hM) :=
  zariskiReadingTensorSquare_pullbackTensor h N M hN hM

/-- Hypothesis 9 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the ninth
square. -/
theorem zariskiReadingTensorSquareMate_9 :
    HypothesisOf₂₀_9 (zariskiReadingTensorSquareMateAux h N M hN hM) :=
  zariskiReadingTensorSquare_restrictPullbackTensor h N M hN hM

/-- Hypothesis 10 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the tenth
square. -/
theorem zariskiReadingTensorSquareMate_10 :
    HypothesisOf₂₀_10 (zariskiReadingTensorSquareMateAux h N M hN hM) :=
  zariskiReadingTensorSquare_restrictPullbackNaturality h N M hN hM

/-- Hypothesis 11 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the naturality
of the counit at the comparison of Stacks 03EL. -/
theorem zariskiReadingTensorSquareMate_11 :
    HypothesisOf₂₀_11 (zariskiReadingTensorSquareMateAux h N M hN hM) :=
  (representedReindexEquivalenceTopos T').counit.naturality _

/-- Hypothesis 20 of `AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`: the naturality
of `AlgebraicGeometry.Space.representedSquareFactorizationTopos` at the comparison of Stacks 04M0
with tensor products. -/
theorem zariskiReadingTensorSquareMate_20 :
    HypothesisOf₂₀_20 (zariskiReadingTensorSquareMateAux h N M hN hM) :=
  (representedSquareFactorizationTopos h).naturality _


end AlgebraicGeometry.Space
