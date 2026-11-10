module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
public import StacksFrontier.CategoryTheory.Sites.Descent.OfRefinement

/-!
# A right adjoint for descent data along a single morphism

Let `F` be a pseudofunctor from the locally discrete bicategory on `C₀ᵒᵖ` to `Cat`, let
`f : X ⟶ Y` be a morphism with a chosen fibre product `sq : X ×_Y X`, and suppose that the
inverse image functors `F.map f` and `F.map sq.p` have right adjoints and that the fibre of `F`
over `Y` has equalizers. This file constructs a right adjoint to the comparison functor
`F.toDescentData (fun _ : Unit ↦ f)`, by the usual formula: the object of `F.obj Y` underlying
a descent datum `D` is the equalizer of the two transposes of the two restrictions of the
canonical map of `D` to the fibre product.

## Main definitions

* `CategoryTheory.Pseudofunctor.reconstructionFirst` and
  `CategoryTheory.Pseudofunctor.reconstructionSecond`: the two morphisms whose equalizer is
  taken;
* `CategoryTheory.Pseudofunctor.singletonDescentRightAdjoint` and
  `CategoryTheory.Pseudofunctor.singletonDescentAdjunction`: the right adjoint and the
  adjunction.

## Main results

* `CategoryTheory.Pseudofunctor.singletonDescentAdjunction_counit_hom`: the component of the
  counit of that adjunction, which is what one tests for invertibility when proving that
  descent is effective;
* `CategoryTheory.equalizerIsoOfCompatibleSquare`: a functor preserving an equalizer carries it
  to the equalizer of a compatible pair, which is how the construction is compared across a
  base change.

## Implementation notes

A morphism from the canonical descent datum of an object `N` of the fibre over `Y` to `D` is a
morphism `F.map f (N) ⟶ D.obj ()` compatible with the gluing data of `D`; transposing it along
the adjunction gives a morphism `N ⟶ R (D.obj ())`, and the compatibility becomes exactly the
equation saying that the transpose equalizes the two reconstruction morphisms. That bijection
is natural, so `CategoryTheory.Adjunction.rightAdjointOfEquiv` produces the adjoint.

The compatibility of a gluing morphism with the two restrictions is reduced to a single
equation on the fibre product by `CategoryTheory.Pseudofunctor.DescentData.comm_of_chosenPullback`;
the transposition step itself is isolated in
`CategoryTheory.Pseudofunctor.equalizer_reconstruction_comm`, which is a statement about two
adjunctions and two commutation isomorphisms and mentions no descent data.

Nothing here carries a Stacks attribute: this is category-theoretic substrate, and the source
states none of it.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃ v v' u u'

/-! ### Transporting an equalizer along a functor -/

/-- A functor preserving the equalizer of a pair carries it to the equalizer of any compatible
pair. -/
noncomputable def equalizerIsoOfCompatibleSquare
    {A : Type u₁} {Bb : Type u₂} [Category.{v₁} A] [Category.{v₂} Bb]
    [HasEqualizers A] [HasEqualizers Bb] (G : A ⥤ Bb)
    {M N : A} (a b : M ⟶ N) [PreservesLimit (parallelPair a b) G]
    {M' N' : Bb} (a' b' : M' ⟶ N')
    (eM : G.obj M ≅ M') (eN : G.obj N ≅ N')
    (ha : G.map a ≫ eN.hom = eM.hom ≫ a')
    (hb : G.map b ≫ eN.hom = eM.hom ≫ b') :
    G.obj (equalizer a b) ≅ equalizer a' b' :=
  PreservesEqualizer.iso G a b ≪≫
    HasLimit.isoOfNatIso (parallelPairIso (G.map a) (G.map b) a' b' eM eN ha hb)

/-- The isomorphism of `CategoryTheory.equalizerIsoOfCompatibleSquare` is compatible with the
two inclusions of the equalizers. -/
theorem equalizerIsoOfCompatibleSquare_hom_ι
    {A : Type u₁} {Bb : Type u₂} [Category.{v₁} A] [Category.{v₂} Bb]
    [HasEqualizers A] [HasEqualizers Bb] (G : A ⥤ Bb)
    {M N : A} (a b : M ⟶ N) [PreservesLimit (parallelPair a b) G]
    {M' N' : Bb} (a' b' : M' ⟶ N')
    (eM : G.obj M ≅ M') (eN : G.obj N ≅ N')
    (ha : G.map a ≫ eN.hom = eM.hom ≫ a')
    (hb : G.map b ≫ eN.hom = eM.hom ≫ b') :
    (equalizerIsoOfCompatibleSquare G a b a' b' eM eN ha hb).hom ≫
        equalizer.ι a' b' = G.map (equalizer.ι a b) ≫ eM.hom := by
  simp [equalizerIsoOfCompatibleSquare, HasLimit.isoOfNatIso_hom_π,
    parallelPairIso, parallelPairIsoMk]

namespace Pseudofunctor

/-! ### Transposing the compatibility of a gluing morphism -/

/-- **Transposing the equalizing condition.** For two adjunctions and two commutation
isomorphisms of the left adjoints with a third functor, a morphism equalizing the two
transposes becomes, after transposition, a morphism commuting with the given isomorphism. -/
theorem equalizer_reconstruction_comm
    {A : Type u₁} {Bb : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} Bb] [Category.{v₃} C]
    {L : A ⥤ Bb} {R : Bb ⥤ A} {P Q : Bb ⥤ C} {K : A ⥤ C} {T : C ⥤ A}
    (adj : L ⊣ R) (adjK : K ⊣ T)
    (eP : K ≅ L ⋙ P) (eQ : K ≅ L ⋙ Q) (M : Bb)
    (α : P.obj M ≅ Q.obj M)
    (a : R.obj M ⟶ T.obj (P.obj M))
    (b : R.obj M ⟶ T.obj (P.obj M))
    (ha : a = adjK.homEquiv _ _ (eP.hom.app _ ≫ P.map (adj.counit.app M)))
    (hb : b = adjK.homEquiv _ _
      (eQ.hom.app _ ≫ Q.map (adj.counit.app M) ≫ α.inv))
    {N : A} (ι : N ⟶ R.obj M) (hι : ι ≫ a = ι ≫ b) :
    P.map (L.map ι ≫ adj.counit.app M) ≫ α.hom =
      eP.inv.app N ≫ eQ.hom.app N ≫ Q.map (L.map ι ≫ adj.counit.app M) := by
  subst a b
  have h : K.map ι ≫ eP.hom.app _ ≫ P.map (adj.counit.app M) =
      K.map ι ≫ eQ.hom.app _ ≫ Q.map (adj.counit.app M) ≫ α.inv := by
    apply (adjK.homEquiv N (P.obj M)).injective
    simpa only [adjK.homEquiv_naturality_left, Functor.id_obj] using hι
  rw [eP.hom.naturality_assoc, eQ.hom.naturality_assoc] at h
  rw [← cancel_epi (eP.hom.app N), ← cancel_mono α.inv]
  simpa only [Functor.map_comp, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Iso.hom_inv_id_app_assoc, Functor.comp_map, Functor.id_obj] using h

/-! ### The reconstruction of an object from a descent datum -/

open DescentData LocallyDiscreteOpToCat

variable {C₀ : Type u} [Category.{v} C₀]
  (F : Pseudofunctor (LocallyDiscrete C₀ᵒᵖ) Cat.{v', u'})
  {X Y : C₀} (f : X ⟶ Y) (sq : ChosenPullback f f)
  {R : F.obj (.mk (.op X)) ⥤ F.obj (.mk (.op Y))}
  (adj : (F.map f.op.toLoc).toFunctor ⊣ R)
  {T : F.obj (.mk (.op sq.pullback)) ⥤ F.obj (.mk (.op Y))}
  (adjK : (F.map sq.p.op.toLoc).toFunctor ⊣ T)

/-- The first of the two morphisms whose equalizer reconstructs an object from a descent datum:
the transpose of the restriction of the counit along the first projection. -/
noncomputable def reconstructionFirst (D : F.DescentData (fun _ : Unit ↦ f)) :
    R.obj (D.obj ()) ⟶ T.obj ((F.map sq.p₁.op.toLoc).toFunctor.obj (D.obj ())) :=
  adjK.homEquiv _ _
    ((F.mapComp' f.op.toLoc sq.p₁.op.toLoc sq.p.op.toLoc (by
      rw [← Quiver.Hom.comp_toLoc, ← op_comp, sq.hp₁])).hom.toNatTrans.app _ ≫
        (F.map sq.p₁.op.toLoc).toFunctor.map (adj.counit.app (D.obj ())))

/-- The second of the two morphisms whose equalizer reconstructs an object from a descent
datum: the transpose of the restriction of the counit along the second projection, corrected by
the gluing isomorphism of the datum. -/
noncomputable def reconstructionSecond (D : F.DescentData (fun _ : Unit ↦ f)) :
    R.obj (D.obj ()) ⟶ T.obj ((F.map sq.p₁.op.toLoc).toFunctor.obj (D.obj ())) :=
  adjK.homEquiv _ _
    ((F.mapComp' f.op.toLoc sq.p₂.op.toLoc sq.p.op.toLoc (by
      rw [← Quiver.Hom.comp_toLoc, ← op_comp, sq.hp₂])).hom.toNatTrans.app _ ≫
        (F.map sq.p₂.op.toLoc).toFunctor.map (adj.counit.app (D.obj ())) ≫
          D.hom sq.p sq.p₂ sq.p₁ sq.hp₂ sq.hp₁)

/-- A morphism into the reconstruction equalizes the two reconstruction morphisms exactly when
the corresponding morphism of descent data is well defined; this is the morphism of descent
data it determines. -/
noncomputable def reconstructionHom
    (D : F.DescentData (fun _ : Unit ↦ f))
    {N : F.obj (.mk (.op Y))} (ι : N ⟶ R.obj (D.obj ()))
    (hι : ι ≫ reconstructionFirst F f sq adj adjK D =
      ι ≫ reconstructionSecond F f sq adj adjK D) :
    (F.toDescentData (fun _ : Unit ↦ f)).obj N ⟶ D where
  hom _ := (F.map f.op.toLoc).toFunctor.map ι ≫ adj.counit.app (D.obj ())
  comm := by
    apply DescentData.comm_of_chosenPullback (fun _ _ ↦ sq)
    intro i j
    cases i
    cases j
    dsimp only [toDescentData, ofObj]
    simpa only [toDescentData_obj, ofObj_hom, DescentData.iso_hom,
      Cat.Hom.toNatIso, Category.assoc] using
      equalizer_reconstruction_comm adj adjK
      (Cat.Hom.toNatIso (F.mapComp' f.op.toLoc sq.p₁.op.toLoc sq.p.op.toLoc (by
        rw [← Quiver.Hom.comp_toLoc, ← op_comp, sq.hp₁])))
      (Cat.Hom.toNatIso (F.mapComp' f.op.toLoc sq.p₂.op.toLoc sq.p.op.toLoc (by
        rw [← Quiver.Hom.comp_toLoc, ← op_comp, sq.hp₂])))
      (D.obj ()) (D.iso sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂)
      _ _ rfl rfl ι hι

/-- **The transpose of a morphism of descent data equalizes the two reconstruction
morphisms.** -/
theorem reconstruction_condition
    (D : F.DescentData (fun _ : Unit ↦ f))
    {N : F.obj (.mk (.op Y))} (φ : (F.toDescentData (fun _ : Unit ↦ f)).obj N ⟶ D) :
    adj.homEquiv _ _ (φ.hom ()) ≫ reconstructionFirst F f sq adj adjK D =
      adj.homEquiv _ _ (φ.hom ()) ≫ reconstructionSecond F f sq adj adjK D := by
  let eP := Cat.Hom.toNatIso (F.mapComp' f.op.toLoc sq.p₁.op.toLoc sq.p.op.toLoc (by
    rw [← Quiver.Hom.comp_toLoc, ← op_comp, sq.hp₁]))
  let eQ := Cat.Hom.toNatIso (F.mapComp' f.op.toLoc sq.p₂.op.toLoc sq.p.op.toLoc (by
    rw [← Quiver.Hom.comp_toLoc, ← op_comp, sq.hp₂]))
  let c : (F.map f.op.toLoc).toFunctor.obj N ⟶ D.obj () := φ.hom ()
  change adj.homEquiv _ _ c ≫ adjK.homEquiv _ _
      (eP.hom.app _ ≫ (F.map sq.p₁.op.toLoc).toFunctor.map (adj.counit.app _)) =
    adj.homEquiv _ _ c ≫ adjK.homEquiv _ _
      (eQ.hom.app _ ≫ (F.map sq.p₂.op.toLoc).toFunctor.map (adj.counit.app _) ≫
        D.hom sq.p sq.p₂ sq.p₁ sq.hp₂ sq.hp₁)
  rw [← adjK.homEquiv_naturality_left, ← adjK.homEquiv_naturality_left]
  apply congrArg (adjK.homEquiv _ _)
  rw [eP.hom.naturality_assoc, eQ.hom.naturality_assoc]
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map]
  simp only [← Functor.map_comp, ← Functor.map_comp_assoc]
  have hc := (adj.homEquiv N (D.obj ())).symm_apply_apply c
  rw [adj.homEquiv_counit] at hc
  rw [hc]
  have h := φ.comm sq.p (i₁ := ()) (i₂ := ()) sq.p₁ sq.p₂ sq.hp₁ sq.hp₂
  dsimp only [toDescentData, ofObj] at h
  rw [← cancel_epi (eP.inv.app N)]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← cancel_mono (D.hom sq.p (i₁ := ()) (i₂ := ()) sq.p₁ sq.p₂ sq.hp₁ sq.hp₂)]
  simp only [Category.assoc]
  rw [D.hom_comp sq.p sq.p₂ sq.p₁ sq.p₂ sq.hp₂ sq.hp₁ sq.hp₂,
    D.hom_self sq.p sq.p₂ sq.hp₂]
  have h' : (F.map sq.p₁.op.toLoc).toFunctor.map c ≫
      D.hom sq.p sq.p₁ sq.p₂ sq.hp₁ sq.hp₂ =
      eP.inv.app N ≫ eQ.hom.app N ≫ (F.map sq.p₂.op.toLoc).toFunctor.map c := by
    simpa only [eP, eQ, c, Cat.Hom.toNatIso, Category.assoc] using h
  exact h'.trans (congrArg (fun z ↦ eP.inv.app N ≫ eQ.hom.app N ≫ z)
    (Category.comp_id ((F.map sq.p₂.op.toLoc).toFunctor.map c)).symm)

/-- **Morphisms into the reconstruction are morphisms of descent data.** -/
noncomputable def reconstructionHomEquiv
    [HasEqualizers (F.obj (.mk (.op Y)))]
    (D : F.DescentData (fun _ : Unit ↦ f)) (N : F.obj (.mk (.op Y))) :
    ((F.toDescentData (fun _ : Unit ↦ f)).obj N ⟶ D) ≃
      (N ⟶ equalizer (reconstructionFirst F f sq adj adjK D)
        (reconstructionSecond F f sq adj adjK D)) where
  toFun φ := equalizer.lift (adj.homEquiv _ _ (φ.hom ()))
    (reconstruction_condition F f sq adj adjK D φ)
  invFun u := reconstructionHom F f sq adj adjK D (u ≫ equalizer.ι _ _)
    (by rw [Category.assoc, equalizer.condition, ← Category.assoc])
  left_inv φ := by
    ext i
    cases i
    dsimp only [reconstructionHom]
    rw [equalizer.lift_ι]
    exact (adj.homEquiv_counit N (D.obj ())
        (adj.homEquiv N (D.obj ()) (φ.hom ()))).symm.trans
      ((adj.homEquiv N (D.obj ())).symm_apply_apply (φ.hom ()))
  right_inv u := by
    apply equalizer.hom_ext
    rw [equalizer.lift_ι]
    dsimp only [reconstructionHom]
    exact (congrArg (adj.homEquiv N (D.obj ()))
        (adj.homEquiv_counit N (D.obj ()) (u ≫ equalizer.ι _ _)).symm).trans
      ((adj.homEquiv N (D.obj ())).apply_symm_apply (u ≫ equalizer.ι _ _))

/-- The bijection of `CategoryTheory.Pseudofunctor.reconstructionHomEquiv` is natural. -/
theorem reconstructionHomEquiv_naturality
    [HasEqualizers (F.obj (.mk (.op Y)))]
    (D : F.DescentData (fun _ : Unit ↦ f))
    {N N' : F.obj (.mk (.op Y))} (u : N' ⟶ N)
    (φ : (F.toDescentData (fun _ : Unit ↦ f)).obj N ⟶ D) :
    reconstructionHomEquiv F f sq adj adjK D N'
        ((F.toDescentData (fun _ : Unit ↦ f)).map u ≫ φ) =
      u ≫ reconstructionHomEquiv F f sq adj adjK D N φ := by
  apply equalizer.hom_ext
  simp only [reconstructionHomEquiv, Equiv.coe_fn_mk, equalizer.lift_ι, Category.assoc]
  exact adj.homEquiv_naturality_left u (φ.hom ())

/-- **The right adjoint of the comparison functor for a singleton family.** -/
noncomputable def singletonDescentRightAdjoint
    [HasEqualizers (F.obj (.mk (.op Y)))] :
    F.DescentData (fun _ : Unit ↦ f) ⥤ F.obj (.mk (.op Y)) :=
  Adjunction.rightAdjointOfEquiv
    (fun N D ↦ reconstructionHomEquiv F f sq adj adjK D N)
    (fun _ _ D u φ ↦ reconstructionHomEquiv_naturality F f sq adj adjK D u φ)

/-- **The comparison functor for a singleton family has a right adjoint.** -/
noncomputable def singletonDescentAdjunction
    [HasEqualizers (F.obj (.mk (.op Y)))] :
    F.toDescentData (fun _ : Unit ↦ f) ⊣ singletonDescentRightAdjoint F f sq adj adjK :=
  Adjunction.adjunctionOfEquivRight _ _

/-- The component of the counit of
`CategoryTheory.Pseudofunctor.singletonDescentAdjunction`. -/
theorem singletonDescentAdjunction_counit_hom
    [HasEqualizers (F.obj (.mk (.op Y)))]
    (D : F.DescentData (fun _ : Unit ↦ f)) :
    ((singletonDescentAdjunction F f sq adj adjK).counit.app D).hom () =
      (F.map f.op.toLoc).toFunctor.map
        (equalizer.ι (reconstructionFirst F f sq adj adjK D)
          (reconstructionSecond F f sq adj adjK D)) ≫ adj.counit.app (D.obj ()) := by
  change (F.map f.op.toLoc).toFunctor.map
    (𝟙 _ ≫ equalizer.ι (reconstructionFirst F f sq adj adjK D)
      (reconstructionSecond F f sq adj adjK D)) ≫ adj.counit.app (D.obj ()) = _
  rw [Category.id_comp]

end Pseudofunctor

end CategoryTheory

end
