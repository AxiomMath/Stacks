module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposCompBilinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompProvider
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateNaturality
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp

/-!
# The comparison of Tag 03EL along a genuine composite of morphisms of ringed topoi

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of ringed topoi in the sense of [Stacks, Tag 01D3],
part (2) (`AlgebraicGeometry.RingedToposHom`).  Two comparisons `(g ∘ f)^* ≅ g^* ⋙ f^*` of
pullbacks of sheaves of modules are in the tree:

* `AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso`, the uniqueness isomorphism of left
  adjoints of the two-field direct images `f_* ⋙ g_*`, which is the one the derived composition
  isomorphism of [Stacks, Tag 0D6D] for a morphism of ringed topoi is built from; and
* `Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` at the composite data
  `AlgebraicGeometry.RingedToposHom.toModulesHomPushforwardIso`, the uniqueness isomorphism of left
  adjoints of the four-field direct images, which is the one the composition law
  `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp` of [Stacks, Tag 03EL] is stated with.

This file proves that they are the same isomorphism (`pullbackModulesCompIso_eq`), and deduces
the composition law of [Stacks, Tag 03EL] for the first one
(`pullbackTensorIso_hom_app_comp_toModulesHom`).

## Implementation notes

*How the two comparisons are compared.*  Both are comparisons of left adjoints, so they agree as
soon as their conjugates for one fixed pair of adjunctions do.  The conjugate of the four-field one
is the four-field comparison of direct images
(`Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom`); that of the two-field
one is computed by `AlgebraicGeometry.RingedToposHom.conjugateEquiv_pullbackModulesCompIso_hom`,
after changing the right adjoints along `AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso`
(`Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight`).  What remains is an identity between
transformations of direct images, each of which is the identity on underlying sheaves of sets.

*Why the identities on underlying sheaves are written as `eqToHom`.*  The two readings of a direct
image, four-field and two-field, have definitionally equal underlying sheaves, but deciding that
equality inside an elaboration problem is expensive.  Each underlying-map lemma below therefore
names the equality of underlying sheaves once (`moduleSheaf_toModulesPushforward_eq` and its two
companions, all `rfl`) and returns the corresponding `eqToHom`, so that the final computation is a
composite of `eqToHom`s and no unification between the two readings is ever attempted.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.RingedToposHom

universe w w' w'' v u v' u' v'' u''

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]

/-- Composing two adjunctions whose right adjoints were changed along isomorphisms. -/
lemma _root_.CategoryTheory.Adjunction.comp_ofNatIsoRight {C D E : Type*} [Category C]
    [Category D] [Category E] {F : C ⥤ D} {G G' : D ⥤ C} {H : D ⥤ E} {I I' : E ⥤ D}
    (a : F ⊣ G) (b : H ⊣ I) (e₁ : G ≅ G') (e₂ : I ≅ I') :
    (a.ofNatIsoRight e₁).comp (b.ofNatIsoRight e₂) =
      (a.comp b).ofNatIsoRight (Functor.isoWhiskerRight e₂ G ≪≫ Functor.isoWhiskerLeft I' e₁) := by
  apply Adjunction.ext
  ext X
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.map_comp, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Category.assoc]
  congr 1
  rw [← G'.map_comp, ← Category.assoc, ← G.map_comp]
  exact (e₁.hom.naturality _).symm


/-- The comparison of the two readings of `f_* ⋙ g_*`. -/
def pushforwardModulesCompFourIso (f : RingedToposHom X Y) (g : RingedToposHom Y Z) :
    Stacks.Sheaves.RingedToposModules.pushforwardModules f.toModulesHom ⋙
        Stacks.Sheaves.RingedToposModules.pushforwardModules g.toModulesHom ≅
      pushforwardModules f ⋙ pushforwardModules g :=
  Functor.isoWhiskerRight f.toModulesPushforwardIso
      (Stacks.Sheaves.RingedToposModules.pushforwardModules g.toModulesHom) ≪≫
    Functor.isoWhiskerLeft (pushforwardModules f) g.toModulesPushforwardIso

omit [X.J.HasSheafCompose (forget RingCat.{w})] in
/-- Three composable `eqToHom`s compose to an `eqToHom`. -/
lemma eqToHom_comp_three {T : Type*} [Category T] {A B C D : T} (p : A = B) (q : B = C)
    (r : C = D) (s : A = D) : (eqToHom p ≫ eqToHom q) ≫ eqToHom r = eqToHom s := by
  subst p q r
  simp

/-- The underlying sheaves of sets of the two readings of the direct image agree. -/
lemma moduleSheaf_toModulesPushforward_eq (f : RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
        ((Stacks.Sheaves.RingedToposModules.pushforwardModules f.toModulesHom).obj F) =
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
        ((pushforwardModules f).obj F) :=
  rfl

/-- On underlying sheaves, the component of `toModulesPushforwardIso.hom` at `F` is the
`eqToHom` of `moduleSheaf_toModulesPushforward_eq`. -/
lemma moduleSheafFunctor_map_toModulesPushforwardIso_hom_app (f : RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        (f.toModulesPushforwardIso.hom.app F) =
      eqToHom (moduleSheaf_toModulesPushforward_eq f F) :=
  Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_ofSheafHom _ _ _

/-- On underlying sheaves, the component of `toModulesPushforwardIso.inv` at `F` is the
`eqToHom` of the inverse of `moduleSheaf_toModulesPushforward_eq`. -/
lemma moduleSheafFunctor_map_toModulesPushforwardIso_inv_app (f : RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        (f.toModulesPushforwardIso.inv.app F) =
      eqToHom (moduleSheaf_toModulesPushforward_eq f F).symm :=
  Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_ofSheafHom _ _ _

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] in
/-- The underlying sheaves of sets of the two sides of the composition isomorphism agree. -/
lemma moduleSheaf_pushforwardModulesComp_eq (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj
        ((pushforwardModules (g.comp f)).obj F) =
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj
        ((pushforwardModules f ⋙ pushforwardModules g).obj F) :=
  rfl

/-- On underlying sheaves, the component of `(pushforwardModulesCompIso f g).inv` at `F` is the
`eqToHom` of the inverse of `moduleSheaf_pushforwardModulesComp_eq`. -/
lemma moduleSheafFunctor_map_pushforwardModulesCompIso_inv_app (f : RingedToposHom X Y)
    (g : RingedToposHom Y Z)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        ((pushforwardModulesCompIso f g).inv.app F) =
      eqToHom (moduleSheaf_pushforwardModulesComp_eq f g F).symm :=
  Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_ofSheafHom _ _ _

/-- The underlying sheaves of sets of the two sides of the four-field composition isomorphism
agree. -/
lemma moduleSheaf_pushforwardModulesCompFour_eq (f : RingedToposHom X Y)
    (g : RingedToposHom Y Z)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj
        ((Stacks.Sheaves.RingedToposModules.pushforwardModules f.toModulesHom ⋙
          Stacks.Sheaves.RingedToposModules.pushforwardModules g.toModulesHom).obj F) =
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj
        ((Stacks.Sheaves.RingedToposModules.pushforwardModules (g.comp f).toModulesHom).obj F) :=
  rfl

/-- On underlying sheaves, the component at `F` of the four-field composition isomorphism of
direct images is the `eqToHom` of `moduleSheaf_pushforwardModulesCompFour_eq`. -/
lemma moduleSheafFunctor_map_pushforwardModulesCompIso_four_hom_app (f : RingedToposHom X Y)
    (g : RingedToposHom Y Z)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
        ((Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso f.toModulesHom
          g.toModulesHom (g.comp f).toModulesHom (toModulesHomPushforwardIso f g)
          (fSharpSetComp_toModulesHomPushforwardIso f g)).hom.app F) =
      eqToHom (moduleSheaf_pushforwardModulesCompFour_eq f g F) :=
  Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_pushforwardModulesCompIso_hom_app
    f.toModulesHom g.toModulesHom (g.comp f).toModulesHom (toModulesHomPushforwardIso f g)
    (fSharpSetComp_toModulesHomPushforwardIso f g) F

/-- The four-field composition isomorphism of direct images along `f` and `g` is the composite of
`pushforwardModulesCompFourIso f g`, the inverse of `pushforwardModulesCompIso f g` and the inverse
of `(g.comp f).toModulesPushforwardIso`. -/
lemma pushforwardModulesCompFourIso_comp (f : RingedToposHom X Y) (g : RingedToposHom Y Z) :
    (pushforwardModulesCompFourIso f g).hom ≫ (pushforwardModulesCompIso f g).inv ≫
        (g.comp f).toModulesPushforwardIso.inv =
      (Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso f.toModulesHom
        g.toModulesHom (g.comp f).toModulesHom (toModulesHomPushforwardIso f g)
        (fSharpSetComp_toModulesHomPushforwardIso f g)).hom := by
  refine NatTrans.ext (funext fun F => ?_)
  apply Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
  simp only [pushforwardModulesCompFourIso, NatTrans.comp_app, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.map_comp,
    Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_pushforwardModules_map,
    moduleSheafFunctor_map_toModulesPushforwardIso_hom_app,
    moduleSheafFunctor_map_toModulesPushforwardIso_inv_app,
    moduleSheafFunctor_map_pushforwardModulesCompIso_inv_app,
    moduleSheafFunctor_map_pushforwardModulesCompIso_four_hom_app, eqToHom_map, eqToHom_trans]
  exact eqToHom_comp_three _ _ _ _

variable
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- The conjugate of `(pullbackModulesCompIso f g).hom` with respect to the four-field
pullback–pushforward adjunctions is the four-field composition isomorphism of direct images. -/
lemma conjugateEquiv_pullbackModulesCompIso_hom_four (f : RingedToposHom X Y)
    (g : RingedToposHom Y Z) :
    conjugateEquiv
        ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom).comp
          (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom))
        (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules (g.comp f).toModulesHom)
        (pullbackModulesCompIso f g).hom =
      (Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso f.toModulesHom
        g.toModulesHom (g.comp f).toModulesHom (toModulesHomPushforwardIso f g)
        (fSharpSetComp_toModulesHomPushforwardIso f g)).hom := by
  have h := conjugateEquiv_pullbackModulesCompIso_hom f g
  rw [pullbackAdjPushforwardModules, pullbackAdjPushforwardModules, pullbackAdjPushforwardModules,
    Adjunction.comp_ofNatIsoRight, Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight] at h
  rw [← pushforwardModulesCompFourIso_comp]
  have h' := congrArg (fun t => (pushforwardModulesCompFourIso f g).hom ≫ t ≫
    (g.comp f).toModulesPushforwardIso.inv) h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h'
  rw [← h']
  simp only [pushforwardModulesCompFourIso, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The comparison `pullbackModulesCompIso f g` equals the four-field comparison
`Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` at the composite data
`toModulesHomPushforwardIso f g`. -/
theorem pullbackModulesCompIso_eq (f : RingedToposHom X Y) (g : RingedToposHom Y Z) :
    pullbackModulesCompIso f g =
      Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso f.toModulesHom g.toModulesHom
        (g.comp f).toModulesHom (toModulesHomPushforwardIso f g)
        (fSharpSetComp_toModulesHomPushforwardIso f g) := by
  refine Iso.ext (Equiv.injective _
    ((conjugateEquiv_pullbackModulesCompIso_hom_four f g).trans ?_))
  symm
  exact Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _


omit [X.J.HasSheafCompose (forget RingCat.{w})] in
/-- If `z ≫ s = ch ≫ x`, `ci ≫ ch = 𝟙 Q` and `s ≫ s' = 𝟙 V`, then `x ≫ s' = ci ≫ z`. -/
lemma comp_eq_inv_comp_of_comp_eq {T : Type*} [Category T] {P Q U V : T}
    (x : Q ⟶ U) (z : P ⟶ V) (ch : P ⟶ Q) (ci : Q ⟶ P) (s : V ⟶ U) (s' : U ⟶ V)
    (h : z ≫ s = ch ≫ x) (hc : ci ≫ ch = 𝟙 Q) (hs : s ≫ s' = 𝟙 V) :
    x ≫ s' = ci ≫ z := by
  calc x ≫ s' = (ci ≫ ch) ≫ x ≫ s' := by rw [hc, Category.id_comp]
    _ = ci ≫ (z ≫ s) ≫ s' := by rw [h]; simp only [Category.assoc]
    _ = ci ≫ z := by rw [Category.assoc, hs, Category.comp_id]

omit [X.J.HasSheafCompose (forget RingCat.{w})] in
/-- A bifunctor applied to a pair of isomorphisms, followed by its two one-variable actions on
the inverses, is the identity. -/
lemma uncurry_map_hom_comp_inv {T C : Type*} [Category T] [Category C] (B : T ⥤ T ⥤ C)
    {a a' b b' : T} (e₁ : a ≅ a') (e₂ : b ≅ b') :
    (Functor.uncurry.obj B).map ((e₁.hom, e₂.hom) : (a, b) ⟶ (a', b')) ≫
        ((B.map e₁.inv).app b' ≫ (B.obj a).map e₂.inv) = 𝟙 _ := by
  have hn := (B.map e₁.inv).naturality e₂.hom
  simp only [Functor.uncurry_obj_map, Category.assoc]
  rw [reassoc_of% hn, ← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, e₁.hom_inv_id]
  simp

variable [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]

/-- **The composition law of [Stacks, Tag 03EL] for a genuine composite of morphisms of ringed
topoi**, against the comparison `pullbackModulesCompIso` of pullbacks.  For sheaves of
`𝒪_Z`-modules `a`, `b`: pulling back the comparison for `g` along `f`, then the comparison for `f`,
then the comparison of pullbacks in each tensor factor, is the comparison of pullbacks at
`a ⊗ b` followed by the comparison for `g ∘ f`.

This is `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp` at the composite data supplied by
`toModulesHomPushforwardIso`, read through `pullbackModulesCompIso_eq` and inverted; the shape is
the degreewise hypothesis of `Stacks.TotalTensorComplexComposite.totalComplexComparison_comp`. -/
theorem pullbackTensorIso_hom_app_comp_toModulesHom (f : RingedToposHom X Y)
    (g : RingedToposHom Y Z)
    (a b : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    f.toModulesHom.pullbackModules.map
          ((Stacks.SheafOfModules.pullbackTensorIso g.toModulesHom).app (a, b)).hom ≫
        ((Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).app
          (g.toModulesHom.pullbackModules.obj a, g.toModulesHom.pullbackModules.obj b)).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
            ((pullbackModulesCompIso f g).symm.hom.app a)).app
              (f.toModulesHom.pullbackModules.obj (g.toModulesHom.pullbackModules.obj b)) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
            ((g.comp f).toModulesHom.pullbackModules.obj a)).map
              ((pullbackModulesCompIso f g).symm.hom.app b)) =
      (pullbackModulesCompIso f g).symm.hom.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor Z.O).obj a).obj b) ≫
        ((Stacks.SheafOfModules.pullbackTensorIso (g.comp f).toModulesHom).app (a, b)).hom := by
  have h := Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp f.toModulesHom g.toModulesHom
    (g.comp f).toModulesHom (toModulesHomPushforwardIso f g)
    (fSharpSetComp_toModulesHomPushforwardIso f g) a b
  rw [← pullbackModulesCompIso_eq] at h
  refine (Category.assoc _ _ _).symm.trans ?_
  exact comp_eq_inv_comp_of_comp_eq _ _ _ _ _ _ h
    ((pullbackModulesCompIso f g).inv_hom_id_app _)
    (uncurry_map_hom_comp_inv (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      ((pullbackModulesCompIso f g).app a)
      ((pullbackModulesCompIso f g).app b))

end AlgebraicGeometry.RingedToposHom

end
