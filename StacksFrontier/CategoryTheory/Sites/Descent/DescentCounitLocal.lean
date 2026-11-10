module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Sites.Descent.PullbackDescentData

/-!
# Recognizing an isomorphism of descent data locally

Let `F` be a pseudofunctor from the locally discrete bicategory on `Cᵒᵖ` to `Cat`. A morphism of
descent data is an isomorphism as soon as all its components are, and — when descent along a
family is effective — a morphism of the fibre over the base is an isomorphism as soon as its
restrictions to the members of the family are. The file also records the behaviour of the
counit of an adjunction under a base change.

## Main results

* `CategoryTheory.Pseudofunctor.descentData_isIso_of_components` and
  `CategoryTheory.Pseudofunctor.isIso_of_descent_components`: the two recognition statements;
* `CategoryTheory.isIso_map_counit_of_isIso_mate`: the image of the counit under a functor is
  an isomorphism as soon as its adjoint mate is;
* `CategoryTheory.mate_app_eq`: the component of an adjoint mate, as a transpose;
* `CategoryTheory.transpose_baseChange_compatible`: the transposes used to reconstruct an object
  from a descent datum are compatible with a base change;
* `CategoryTheory.Pseudofunctor.isoMapOfCommSq_eq_comp`,
  `CategoryTheory.Pseudofunctor.square_comp_coherence` and
  `CategoryTheory.Pseudofunctor.square_descent_compatible`: coherences of the comparison
  isomorphisms attached to commutative squares.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Opposite

universe t v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ v v' u u'

namespace Pseudofunctor

/-! ### Isomorphisms of descent data -/

/-- **A morphism of descent data with isomorphism components is an isomorphism.** -/
theorem descentData_isIso_of_components {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {Y : C} {I : Type t} {Z : I → C} {g : ∀ i, Z i ⟶ Y}
    {D E : F.DescentData g} (φ : D ⟶ E) (hφ : ∀ i, IsIso (φ.hom i)) : IsIso φ := by
  have (i : I) : IsIso (φ.hom i) := hφ i
  let e := DescentData.isoMk (fun i ↦ asIso (φ.hom i)) φ.comm
  have he : e.hom = φ := by ext; rfl
  rw [← he]
  infer_instance

/-- **A morphism of the fibre over the base is an isomorphism as soon as its restrictions to the
members of a family of effective descent are.** -/
theorem isIso_of_descent_components {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {Y : C} {I : Type t} {Z : I → C} (g : ∀ i, Z i ⟶ Y)
    (hg : (F.toDescentData g).IsEquivalence)
    {M N : F.obj (.mk (.op Y))} (φ : M ⟶ N)
    (hφ : ∀ i, IsIso ((F.map (g i).op.toLoc).toFunctor.map φ)) : IsIso φ := by
  have := hg
  have := descentData_isIso_of_components F ((F.toDescentData g).map φ) hφ
  exact isIso_of_reflects_iso φ (F.toDescentData g)

end Pseudofunctor

/-! ### The counit of an adjunction after a base change -/

/-- The counit applied to the image of a morphism under `homEquiv` recovers the morphism. -/
private theorem map_homEquiv_comp_counit {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    F.map (adj.homEquiv X Y f) ≫ adj.counit.app Y = f := by
  rw [← adj.homEquiv_counit _ _ (adj.homEquiv X Y f), Equiv.symm_apply_apply]

/-- **The image of a counit is an isomorphism as soon as its adjoint mate is.** -/
theorem isIso_map_counit_of_isIso_mate
    {A : Type u₁} {Bb : Type u₂} {A' : Type u₃} {B' : Type u₄}
    [Category.{v₁} A] [Category.{v₂} Bb] [Category.{v₃} A'] [Category.{v₄} B']
    {L : A ⥤ Bb} {R : Bb ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : A ⥤ A') (H : Bb ⥤ B')
    (e : L ⋙ H ≅ G ⋙ L') (M : Bb) [L'.IsEquivalence]
    (hmate : IsIso (adj'.homEquiv _ _
      (e.inv.app (R.obj M) ≫ H.map (adj.counit.app M)))) :
    IsIso (H.map (adj.counit.app M)) := by
  have := hmate
  have := map_homEquiv_comp_counit adj' (e.inv.app (R.obj M) ≫ H.map (adj.counit.app M))
  have : IsIso (e.inv.app (R.obj M) ≫ H.map (adj.counit.app M)) := by
    rw [← this]
    infer_instance
  have he : H.map (adj.counit.app M) = e.hom.app (R.obj M) ≫
      (e.inv.app (R.obj M) ≫ H.map (adj.counit.app M)) := by simp
  rw [he]
  infer_instance

/-- The component of an adjoint mate is the transpose of the component of the square followed
by the counit. -/
theorem mate_app_eq {A : Type u₁} {Bb : Type u₂} {C : Type u₃} {D : Type u₄}
    [Category.{v₁} A] [Category.{v₂} Bb] [Category.{v₃} C] [Category.{v₄} D]
    {L : A ⥤ Bb} {R : Bb ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') {G : A ⥤ C} {H : Bb ⥤ D}
    (s : TwoSquare G L L' H) (M : Bb) :
    (mateEquiv a b s).app M =
      b.homEquiv _ _ (s.app (R.obj M) ≫ H.map (a.counit.app M)) := by
  apply (b.homEquiv _ _).symm.injective
  exact (b.homEquiv_counit _ _ _).trans ((mateEquiv_counit a b s M).trans
    ((b.homEquiv _ _).symm_apply_apply _).symm)

namespace Pseudofunctor

/-! ### Coherences of the comparison isomorphisms of commutative squares -/

/-- The comparison isomorphism attached to a commutative square, written out through the two
composition constraints and the identification of the two composites. -/
theorem isoMapOfCommSq_eq_comp {E : Type u} [Category.{v} E]
    (F : Pseudofunctor (LocallyDiscrete Eᵒᵖ) Cat)
    {X X' Y Y' : E} {i : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (w : i ≫ f = f' ≫ g) :
    F.isoMapOfCommSq (CommSq.mk w).op.toLoc =
      (F.mapComp g.op.toLoc f'.op.toLoc).symm ≪≫
        eqToIso (congrArg (fun k : X' ⟶ Y ↦ F.map k.op.toLoc) w.symm) ≪≫
          F.mapComp f.op.toLoc i.op.toLoc := by
  simp only [Pseudofunctor.isoMapOfCommSq, Pseudofunctor.mapComp']
  congr 2
  rw [PrelaxFunctor.map₂Iso_eqToIso]
  rfl

/-- **The comparison isomorphisms of two composable commutative squares cohere.** -/
theorem square_comp_coherence {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {X X' Y Y' Z Z' : C}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (p : X' ⟶ X) (q : X' ⟶ Y')
    (r : Z ⟶ X) (k : Z ⟶ Y) (j : Z' ⟶ Z) (r' : Z' ⟶ X') (k' : Z' ⟶ Y')
    (hw : p ≫ f = q ≫ g) (hr : r ≫ f = k) (hr' : r' ≫ q = k')
    (hs : r' ≫ p = j ≫ r) (hk : j ≫ k = k' ≫ g)
    (W : F.obj (.mk (.op Y))) :
    (F.isoMapOfCommSq (CommSq.mk hk).op.toLoc).hom.toNatTrans.app W ≫
      (F.map j.op.toLoc).toFunctor.map
        ((F.mapComp' f.op.toLoc r.op.toLoc k.op.toLoc (by grind)).hom.toNatTrans.app W) ≫
      (F.isoMapOfCommSq (CommSq.mk hs).op.toLoc).hom.toNatTrans.app
        ((F.map f.op.toLoc).toFunctor.obj W) =
    (F.mapComp' q.op.toLoc r'.op.toLoc k'.op.toLoc (by grind)).hom.toNatTrans.app
        ((F.map g.op.toLoc).toFunctor.obj W) ≫
      (F.map r'.op.toLoc).toFunctor.map
        ((F.isoMapOfCommSq (CommSq.mk hw).op.toLoc).hom.toNatTrans.app W) := by
  rw [F.isoMapOfCommSq_eq (CommSq.mk hk).op.toLoc (j ≫ k).op.toLoc (by grind),
    F.isoMapOfCommSq_eq (CommSq.mk hs).op.toLoc (j ≫ r).op.toLoc (by grind),
    F.isoMapOfCommSq_eq (CommSq.mk hw).op.toLoc (p ≫ f).op.toLoc (by grind)]
  dsimp only [Iso.trans_hom, Iso.symm_hom, Cat.Hom.toNatTrans_comp,
    NatTrans.comp_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
    f.op.toLoc r.op.toLoc j.op.toLoc k.op.toLoc (j ≫ r).op.toLoc
    (j ≫ k).op.toLoc (by grind) (by grind) (by grind)]
  simp only [Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  rw [← F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app
    f.op.toLoc p.op.toLoc r'.op.toLoc (p ≫ f).op.toLoc (j ≫ r).op.toLoc
    (j ≫ k).op.toLoc (by grind) (by grind) (by grind)]
  rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc
    g.op.toLoc q.op.toLoc r'.op.toLoc (p ≫ f).op.toLoc k'.op.toLoc
    (j ≫ k).op.toLoc (by grind) (by grind) (by grind)]

/-- **The gluing data of a descent datum is compatible with a base change.** -/
theorem square_descent_compatible {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {X X' Y Y' Z Z' : C}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (p : X' ⟶ X) (q : X' ⟶ Y')
    (r₁ r₂ : Z ⟶ X) (k : Z ⟶ Y) (j : Z' ⟶ Z)
    (r₁' r₂' : Z' ⟶ X') (k' : Z' ⟶ Y')
    (hw : p ≫ f = q ≫ g) (hr₁ : r₁ ≫ f = k) (hr₂ : r₂ ≫ f = k)
    (hr₁' : r₁' ≫ q = k') (hr₂' : r₂' ≫ q = k')
    (hs₁ : r₁' ≫ p = j ≫ r₁) (hs₂ : r₂' ≫ p = j ≫ r₂)
    (hk : j ≫ k = k' ≫ g) (D : F.DescentData (fun _ : Unit ↦ f)) :
    (F.map j.op.toLoc).toFunctor.map (D.hom k (i₁ := ()) (i₂ := ()) r₂ r₁ hr₂ hr₁) ≫
      (F.isoMapOfCommSq (CommSq.mk hs₁).op.toLoc).hom.toNatTrans.app (D.obj ()) =
    (F.isoMapOfCommSq (CommSq.mk hs₂).op.toLoc).hom.toNatTrans.app (D.obj ()) ≫
      ((Pseudofunctor.DescentData.pullFunctor F (f := fun _ : Unit ↦ f)
        (f' := fun _ : Unit ↦ q) (p := g) (α := fun _ ↦ ()) (p' := fun _ ↦ p)
        (fun _ ↦ hw)).obj D).hom k' (i₁ := ()) (i₂ := ()) r₂' r₁' hr₂' hr₁' := by
  rw [F.isoMapOfCommSq_eq (CommSq.mk hs₁).op.toLoc (j ≫ r₁).op.toLoc (by grind),
    F.isoMapOfCommSq_eq (CommSq.mk hs₂).op.toLoc (j ≫ r₂).op.toLoc (by grind)]
  dsimp only [Pseudofunctor.DescentData.pullFunctor,
    Pseudofunctor.DescentData.pullFunctorObj]
  rw [Pseudofunctor.DescentData.pullFunctorObjHom_eq
    (f' := fun _ : Unit ↦ q) (p := g) (α := fun _ : Unit ↦ ())
    (p' := fun _ : Unit ↦ p) (fun _ : Unit ↦ hw) D
    (r₂' ≫ q) (j₁ := ()) (j₂ := ()) r₂' r₁'
    (j ≫ k) (j ≫ r₂) (j ≫ r₁) rfl (hr₁'.trans hr₂'.symm)
    (by rw [hr₂', hk]) hs₂ hs₁]
  rw [← D.pullHom_hom j k (j ≫ k) rfl r₂ r₁ hr₂ hr₁
    (j ≫ r₂) (j ≫ r₁) rfl rfl]
  simp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Cat.Hom.toNatTrans_comp,
    Category.assoc]

end Pseudofunctor

/-- **The reconstruction transposes are compatible with a base change.** Transposing the
restriction of a counit along an adjunction commutes with a base change, given that the two mates
`β` and `γ` of the commutation isomorphisms are compatible with the counits and that the three
commutation isomorphisms satisfy one coherence. -/
theorem transpose_baseChange_compatible
    {A Bb C A' B' C' : Type u}
    [Category.{v} A] [Category.{v} Bb] [Category.{v} C]
    [Category.{v} A'] [Category.{v} B'] [Category.{v} C']
    {L : A ⥤ Bb} {R : Bb ⥤ A} {K : A ⥤ C} {T : C ⥤ A}
    {L' : A' ⥤ B'} {R' : B' ⥤ A'} {K' : A' ⥤ C'} {T' : C' ⥤ A'}
    (a : L ⊣ R) (b : K ⊣ T) (a' : L' ⊣ R') (b' : K' ⊣ T')
    (G : A ⥤ A') (H : Bb ⥤ B') (J : C ⥤ C')
    (P : Bb ⥤ C) (P' : B' ⥤ C') (e : K ≅ L ⋙ P) (e' : K' ≅ L' ⋙ P')
    (s : P ⋙ J ≅ H ⋙ P')
    (c : G ⋙ L' ≅ L ⋙ H) (d : G ⋙ K' ≅ K ⋙ J)
    (β : R ⋙ G ⟶ H ⋙ R') (γ : T ⋙ G ⟶ J ⋙ T')
    (hβ : ∀ M, L'.map (β.app M) ≫ a'.counit.app (H.obj M) =
      c.hom.app (R.obj M) ≫ H.map (a.counit.app M))
    (hγ : ∀ N, K'.map (γ.app N) ≫ b'.counit.app (J.obj N) =
      d.hom.app (T.obj N) ≫ J.map (b.counit.app N))
    (he : ∀ W, d.hom.app W ≫ J.map (e.hom.app W) ≫ s.hom.app (L.obj W) =
      e'.hom.app (G.obj W) ≫ P'.map (c.hom.app W))
    (M : Bb) (N : C) (N' : C') (z : P.obj M ⟶ N) (z' : P'.obj (H.obj M) ⟶ N')
    (n : J.obj N ⟶ N') (hz : J.map z ≫ n = s.hom.app M ≫ z') :
    G.map (b.homEquiv _ _ (e.hom.app (R.obj M) ≫ P.map (a.counit.app M) ≫ z)) ≫
        γ.app N ≫ T'.map n =
      β.app M ≫ b'.homEquiv _ _
        (e'.hom.app (R'.obj (H.obj M)) ≫ P'.map (a'.counit.app (H.obj M)) ≫ z') := by
  apply (b'.homEquiv ((R ⋙ G).obj M) N').symm.injective
  simp only [Functor.id_obj] at *
  change (b'.homEquiv ((R ⋙ G).obj M) N').symm
        (G.map (b.homEquiv (R.obj M) N
          (e.hom.app (R.obj M) ≫ P.map (a.counit.app M) ≫ z)) ≫ γ.app N ≫ T'.map n) =
      (b'.homEquiv ((R ⋙ G).obj M) N').symm (β.app M ≫
        b'.homEquiv ((H ⋙ R').obj M) N'
          (e'.hom.app (R'.obj (H.obj M)) ≫ P'.map (a'.counit.app (H.obj M)) ≫ z'))
  rw [b'.homEquiv_naturality_left_symm (β.app M)]
  dsimp only [Functor.comp_obj]
  rw [Equiv.symm_apply_apply]
  rw [b'.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  have hcn : K'.map (T'.map n) ≫ b'.counit.app N' = b'.counit.app (J.obj N) ≫ n :=
    b'.counit.naturality n
  rw [hcn]
  rw [← Category.assoc (K'.map (γ.app N)), hγ]
  simp only [Category.assoc]
  have hdn : K'.map (G.map (b.homEquiv (R.obj M) N
          (e.hom.app (R.obj M) ≫ P.map (a.counit.app M) ≫ z))) ≫
        d.hom.app (T.obj N) ≫ (J.map (b.counit.app N) ≫ n) =
      d.hom.app (R.obj M) ≫ J.map (K.map (b.homEquiv (R.obj M) N
        (e.hom.app (R.obj M) ≫ P.map (a.counit.app M) ≫ z))) ≫
          (J.map (b.counit.app N) ≫ n) :=
    d.hom.naturality_assoc _ _
  rw [hdn]
  rw [← J.map_comp_assoc, map_homEquiv_comp_counit b]
  simp only [Functor.map_comp, Category.assoc]
  rw [hz]
  have hsn : J.map (P.map (a.counit.app M)) ≫ s.hom.app M ≫ z' =
      s.hom.app (L.obj (R.obj M)) ≫ P'.map (H.map (a.counit.app M)) ≫ z' :=
    s.hom.naturality_assoc _ _
  rw [hsn]
  rw [reassoc_of% (he (R.obj M))]
  rw [e'.hom.naturality_assoc]
  dsimp only [Functor.comp_map]
  simp only [← P'.map_comp_assoc, hβ]

end CategoryTheory

end
