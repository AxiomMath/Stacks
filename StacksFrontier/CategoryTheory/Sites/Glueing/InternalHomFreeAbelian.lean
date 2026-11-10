module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Glueing.SheafHomContravariant
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.AbelianPushPull
public import StacksFrontier.Homology.Injectives.Sheaf.InternalHomExact

/-!
# The abelian internal hom out of a free abelian sheaf is the primed internal hom

Let `(C, J)` be a small site, `P` a presheaf of sets on `C` and `F` an abelian sheaf. There are
two internal homs in play. The abelian one of Stacks 0D7X, `ℋom(A, F)`, has sections
`Mor_{Ab(C/U)}(A|_U, F|_U)` over `U`; the primed one of Stacks 04TP, `ℋom'(G, F)`, has sections
`Mor_{Sh(C/U)}(G|_U, F|_U)` and carries the abelian-group structure of `F`. This file proves that
the two agree once the source is made free:
`ℋom(**Z**_P^#, F) ≅ ℋom'(P^#, F)`, naturally and contravariantly in `P`.

## Main definitions

* `CategoryTheory.Presheaf.freeAbelianSheafOverPullbackIso`: the free abelian sheaf commutes with
  restriction to a localized site, `(**Z**_P^#)|_V ≅ **Z**_{P|_V}^#`, naturally in `P`.
* `CategoryTheory.Presheaf.sheafificationOverPullbackIso`: the same for the sheafification of a
  presheaf of sets, `(P^#)|_V ≅ (P|_V)^#`.
* `CategoryTheory.toFreeAbelianSheaf`: the canonical map `P^# ⟶ **Z**_P^#` of sheaves of sets,
  natural in the presheaf `P`.
* `CategoryTheory.internalHomFreeAbelianHom`: the comparison
  `ℋom(**Z**_P^#, F) ⟶ ℋom'(P^#, F)`, a morphism of abelian sheaves.
* `CategoryTheory.abelianSheafHomPrimeDiagram`: `P ↦ ℋom'(P^#, F)`, the right-hand side as a
  contravariant functor of the presheaf `P`.

## Main results

* `CategoryTheory.internalHomFreeAbelianIso`: **the comparison**
  `ℋom(**Z**_P^#, F) ≅ ℋom'(P^#, F)`, as an isomorphism of functors of `P`.
* `CategoryTheory.sheafHomPrimeEval_add`: the addition on the sections of `ℋom'(G, F)`, which the
  abelian reading of Stacks 04DB puts there, is the pointwise addition of `F`.
* `CategoryTheory.internalHomFreeAbelianSectionEquiv`: the chain of bijections computing the
  sections of `ℋom(**Z**_P^#, F)`, and `internalHomFreeAbelianSectionEquiv_eq`, which identifies
  it with the comparison; hence `isIso_internalHomFreeAbelianHom`.
* `CategoryTheory.sheafHomContraMap_app_hom_app`: the contravariant action of `SheafHom` on
  sections is precomposition, which is what makes the comparison natural in `P`.

## Implementation notes

The comparison is built as a morphism of abelian sheaves in the direction
`ℋom(**Z**_P^#, F) ⟶ ℋom'(P^#, F)` and then shown to be an isomorphism because it is bijective on
every section group. Building it in that direction is what makes naturality in `U` — and in `P` —
a formality: a section of `ℋom(**Z**_P^#, F)` over `U` is a map `(**Z**_P^#)|_U ⟶ F|_U` of abelian
sheaves on `C/U`, and the comparison simply restricts it along the canonical map
`P^# ⟶ **Z**_P^#` of sheaves of sets, which is a single morphism on the site itself. The opposite
direction would have to invoke the comparison of the free abelian sheaf with restriction
separately over each `U`, whose compatibility with the restriction maps is not available.

Bijectivity over a fixed `U` is then the composite of three bijections: the free abelian sheaf
commutes with restriction (`Presheaf.freeAbelianSheafOverPullbackIso`), the free abelian sheaf is
left adjoint to the underlying presheaf of sets (`Presheaf.freeAbelianSheafAdj`), and
sheafification is left adjoint to the inclusion of sheaves; no compatibility of these with the
restriction maps of the two sheaves is needed.

The additivity of the comparison is the one place where the abelian reading of Stacks 04DB has to
be computed: the group structure on the sections of `ℋom'(G, F)` is the one obtained by applying
`SheafHom(G, -)` to the internal addition of `F`, and `sheafHomPrime_add_app` identifies it with
the pointwise addition.

## References

* [Stacks Project, Tag 0D7X](https://stacks.math.columbia.edu/tag/0D7X)
* [Stacks Project, Tag 04TP](https://stacks.math.columbia.edu/tag/04TP)
* [Stacks Project, Tag 04DB](https://stacks.math.columbia.edu/tag/04DB)
* [Stacks Project, Tag 0D86](https://stacks.math.columbia.edu/tag/0D86)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

/-- Equal morphisms of functors into a concrete category agree on every element of every
component. -/
private theorem congr_app_apply {I D : Type*} [Category I] [Category D] {FD : D → D → Type*}
    {CD : D → Type*} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    {F G : I ⥤ D} {α β : F ⟶ G} (h : α = β) (i : I) (x : ToType (F.obj i)) :
    α.app i x = β.app i x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app h i) x

namespace Presheaf

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- **Sheafification commutes with restriction to a localized site**: for `V` an object of `C`,
the restriction to `C / V` of the sheafification of a presheaf of sets is the sheafification of
its restriction, naturally in the presheaf.

This is `CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility` for the
forgetful functor `C / V ⥤ C`, which is both continuous and cocontinuous. -/
def sheafificationOverPullbackIso (V : C) :
    presheafToSheaf J (Type u) ⋙ J.overPullback (Type u) V ≅
      (Functor.whiskeringLeft _ _ _).obj (Over.forget V).op ⋙
        presheafToSheaf (J.over V) (Type u) :=
  ((Over.forget V).pushforwardContinuousSheafificationCompatibility
    (Type u) (J.over V) J).symm

/-- **The free abelian sheaf commutes with restriction to a localized site**: for `V` an object
of `C`, `(**Z**_P^#)|_V ≅ **Z**_{P|_V}^#`, naturally in the presheaf of sets `P`.

Restriction to `C / V` is precomposition with `(Over.forget V).op`, so it commutes with the
sectionwise free abelian group by associativity of composition of functors; that it commutes with
sheafification is
`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility`. -/
def freeAbelianSheafOverPullbackIso (V : C) :
    freeAbelianSheaf J ⋙ J.overPullback AddCommGrpCat.{u} V ≅
      (Functor.whiskeringLeft _ _ _).obj (Over.forget V).op ⋙ freeAbelianSheaf (J.over V) :=
  (Functor.isoWhiskerLeft (freeAbelian : (Cᵒᵖ ⥤ Type u) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}))
    ((Over.forget V).pushforwardContinuousSheafificationCompatibility
      AddCommGrpCat.{u} (J.over V) J)).symm

/-- The unit of the free-abelian-sheaf adjunction is the sectionwise unit of the free abelian
group followed by the map to the sheafification. -/
theorem freeAbelianSheafAdj_unit_app (Q : Cᵒᵖ ⥤ Type u) :
    (freeAbelianSheafAdj J).unit.app Q =
      freeAbelianAdj.unit.app Q ≫
        Functor.whiskerRight (toSheafify J (freeAbelian.obj Q)) (forget AddCommGrpCat.{u}) := by
  rw [freeAbelianSheafAdj, Adjunction.comp_unit_app]
  rfl

/-- **The unit of the free-abelian-sheaf adjunction commutes with restriction to a localized
site.** Restricting the canonical map `P ⟶ **Z**_P^#` to `C / V` is the canonical map
`P|_V ⟶ **Z**_{P|_V}^#` followed by the comparison of `freeAbelianSheafOverPullbackIso`. -/
theorem whiskerLeft_freeAbelianSheafAdj_unit_app (V : C) (Q : Cᵒᵖ ⥤ Type u) :
    Functor.whiskerLeft (Over.forget V).op ((freeAbelianSheafAdj J).unit.app Q) =
      (freeAbelianSheafAdj (J.over V)).unit.app ((Over.forget V).op ⋙ Q) ≫
        Functor.whiskerRight ((freeAbelianSheafOverPullbackIso J V).inv.app Q).hom
          (forget AddCommGrpCat.{u}) := by
  have h := (Over.forget V).toSheafify_pullbackSheafificationCompatibility
    AddCommGrpCat.{u} (J.over V) J (freeAbelian.obj Q)
  ext W x
  have h1 := congr_app_apply (freeAbelianSheafAdj_unit_app J Q) (op W.unop.left) x
  have h2 := congr_app_apply (freeAbelianSheafAdj_unit_app (J.over V) ((Over.forget V).op ⋙ Q)) W x
  have h3 := congr_app_apply h W ((freeAbelianAdj.unit.app Q).app (op W.unop.left) x)
  exact h1.trans (h3.symm.trans (congrArg
    (fun z => (((freeAbelianSheafOverPullbackIso J V).inv.app Q).hom.app W) z) h2.symm))

end Presheaf

/-- A function between additive groups which preserves addition preserves zero. -/
theorem map_zero_of_map_add {M N : Type*} [AddZeroClass M] [AddGroup N] (f : M → N)
    (h : ∀ a b, f (a + b) = f a + f b) : f 0 = 0 := by
  have h0 := h 0 0
  rw [add_zero] at h0
  simpa using h0

/-- Addition of morphisms of presheaves of abelian groups is computed sectionwise. -/
theorem natTrans_add_app_apply {D : Type u} [Category.{u} D] {X Y : D ⥤ AddCommGrpCat.{u}}
    (α β : X ⟶ Y) (Z : D) (x : X.obj Z) :
    (α + β).app Z x = α.app Z x + β.app Z x := by
  simp

/-- Two equal morphisms of sheaves of sets agree on every section. -/
theorem sheafHom_congr_app {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {X Y : Sheaf K (Type u)} {f g : X ⟶ Y} (h : f = g) (Z : Dᵒᵖ) (x : X.obj.obj Z) :
    f.hom.app Z x = g.hom.app Z x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun m : X ⟶ Y => m.hom) h) Z) x

section SheafHomPrime

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

attribute [local instance] sheafTypeCartesian sheafTypeBraided

attribute [local instance] Functor.Braided.ofChosenFiniteProducts

/-- A section of `G ⨯ X` whose two components are `g` and `x` is `pair G X g x`. -/
private theorem eq_pair_of_fst_snd {G X : Sheaf J (Type u)} {Z : Cᵒᵖ} (z : (G ⨯ X).obj.obj Z)
    (g : G.obj.obj Z) (x : X.obj.obj Z) (hg : (prod.fst : G ⨯ X ⟶ G).hom.app Z z = g)
    (hx : (prod.snd : G ⨯ X ⟶ X).hom.app Z z = x) : z = SheafHomAdj.pair G X g x :=
  (SheafHomAdj.pair_fst_snd G X z).symm.trans (congrArg₂ (SheafHomAdj.pair G X) hg hx)

/-- **The lax-monoidal comparison of `SheafHom(G, -)` is the pairing of two maps.** A pair of
sections of `SheafHom(G, X)` and `SheafHom(G, Y)` over `U` is a pair of maps `G|_U ⟶ X|_U` and
`G|_U ⟶ Y|_U`; the comparison sends it to the map `G|_U ⟶ (X ⨯ Y)|_U` whose two components are
the given ones. -/
theorem sheafHomFunctor_μ_app (𝒢 X Y : Sheaf J (Type u)) (U : Cᵒᵖ)
    (x : ((SheafHomAdj.sheafHomFunctor 𝒢).obj X).obj.obj U)
    (y : ((SheafHomAdj.sheafHomFunctor 𝒢).obj Y).obj.obj U)
    (W : (Over U.unop)ᵒᵖ) (s : 𝒢.obj.obj (op (unop W).left)) :
    ((Functor.LaxMonoidal.μ (SheafHomAdj.sheafHomFunctor 𝒢) X Y).hom.app U
        (SheafHomAdj.pair _ _ x y)).hom.app W s =
      SheafHomAdj.pair X Y (x.hom.app W s) (y.hom.app W s) := by
  have hfst : (Functor.LaxMonoidal.μ (SheafHomAdj.sheafHomFunctor 𝒢) X Y).hom.app U
        (SheafHomAdj.pair _ _ x y) ≫
      (J.overPullback (Type u) U.unop).map (prod.fst : X ⨯ Y ⟶ X) = x :=
    (sheafHom_congr_app (Functor.Monoidal.μ_fst (F := SheafHomAdj.sheafHomFunctor 𝒢) X Y) U
      (SheafHomAdj.pair _ _ x y)).trans (SheafHomAdj.fst_pair _ _ x y)
  have hsnd : (Functor.LaxMonoidal.μ (SheafHomAdj.sheafHomFunctor 𝒢) X Y).hom.app U
        (SheafHomAdj.pair _ _ x y) ≫
      (J.overPullback (Type u) U.unop).map (prod.snd : X ⨯ Y ⟶ Y) = y :=
    (sheafHom_congr_app (Functor.Monoidal.μ_snd (F := SheafHomAdj.sheafHomFunctor 𝒢) X Y) U
      (SheafHomAdj.pair _ _ x y)).trans (SheafHomAdj.snd_pair _ _ x y)
  exact eq_pair_of_fst_snd J _ _ _ (sheafHom_congr_app hfst W s) (sheafHom_congr_app hsnd W s)

/-- Evaluation of a section of the primed internal hom `ℋom'(G, F)` over `U`. Such a section is a
morphism `G|_U ⟶ F|_U` of sheaves of sets on the localized site `C / U`, and this evaluates it at
a section of `G` over an object of `C / U`. -/
def sheafHomPrimeEval (𝒢 : Sheaf J (Type u)) (F : Sheaf J AddCommGrpCat.{u}) (U : Cᵒᵖ)
    (a : ((AbelianSheafReading.endofunctor J (SheafHomAdj.sheafHomFunctor 𝒢)).obj F).obj.obj U)
    (W : (Over U.unop)ᵒᵖ) (s : 𝒢.obj.obj (op (unop W).left)) :
    F.obj.obj (op (unop W).left) :=
  (Additive.toMul a).hom.app W s

/-- **The addition on the sections of the primed internal hom is the pointwise addition.** The
abelian reading of Stacks 04DB equips the sections of `ℋom'(G, F)` with the group structure
obtained by applying `SheafHom(G, -)` to the internal addition of `F`; evaluated at a section of
`G` it is the addition of `F`. -/
theorem sheafHomPrimeEval_add (𝒢 : Sheaf J (Type u)) (F : Sheaf J AddCommGrpCat.{u}) (U : Cᵒᵖ)
    (a b : ((AbelianSheafReading.endofunctor J (SheafHomAdj.sheafHomFunctor 𝒢)).obj F).obj.obj U)
    (W : (Over U.unop)ᵒᵖ) (s : 𝒢.obj.obj (op (unop W).left)) :
    sheafHomPrimeEval J 𝒢 F U (a + b) W s =
      sheafHomPrimeEval J 𝒢 F U a W s + sheafHomPrimeEval J 𝒢 F U b W s := by
  have h1 := sheafHom_congr_app
    (AbelianSheafReading.endofunctor_add J (SheafHomAdj.sheafHomFunctor 𝒢) F U a b) W s
  refine h1.trans ((congrArg
    (fun t => (MonObj.mul (X := ((Sites.AbelianSheaf.internalSheaf J).obj F).X)).hom.app
      (op (unop W).left) t)
    (sheafHomFunctor_μ_app J 𝒢 _ _ U (Additive.toMul a) (Additive.toMul b) W s)).trans
    (AbelianSheafReading.internalSheaf_mul_pair_app J F _ _ _))

/-- The sections of `ℋom'(G, F)` over `U` are exactly the morphisms `G|_U ⟶ F|_U` of sheaves of
sets on the localized site `C / U`; this records the identification, so that the abelian-group
structure which the abelian reading puts on them can be named. -/
def sheafHomPrimeSectionsEquiv (𝒢 : Sheaf J (Type u)) (F : Sheaf J AddCommGrpCat.{u}) (U : Cᵒᵖ) :
    ((J.overPullback (Type u) U.unop).obj 𝒢 ⟶
        (J.overPullback (Type u) U.unop).obj
          ((sheafCompose J (forget AddCommGrpCat.{u})).obj F)) ≃
      ((AbelianSheafReading.endofunctor J (SheafHomAdj.sheafHomFunctor 𝒢)).obj F).obj.obj U :=
  Equiv.refl _

/-- The unit of the free-abelian-sheaf adjunction, with its target written as the underlying
presheaf of sets of the free abelian sheaf. -/
def toFreeAbelianSheafUnit (P : Cᵒᵖ ⥤ Type u) :
    P ⟶ (sheafToPresheaf J (Type u)).obj
      ((Presheaf.freeAbelianSheaf J ⋙ sheafCompose J (forget AddCommGrpCat.{u})).obj P) :=
  (Presheaf.freeAbelianSheafAdj J).unit.app P

/-- The unit of the free-abelian-sheaf adjunction is natural in the presheaf. -/
theorem toFreeAbelianSheafUnit_naturality {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q) :
    f ≫ toFreeAbelianSheafUnit J Q =
      toFreeAbelianSheafUnit J P ≫ (sheafToPresheaf J (Type u)).map
        ((Presheaf.freeAbelianSheaf J ⋙ sheafCompose J (forget AddCommGrpCat.{u})).map f) :=
  (Presheaf.freeAbelianSheafAdj J).unit.naturality f

/-- The canonical map from the sheafification of a presheaf of sets `P` to the underlying sheaf of
sets of the free abelian sheaf on `P`, natural in `P`: the map `P ⟶ **Z**_P^#` of presheaves of
sets, extended to the sheafification of `P`. -/
def toFreeAbelianSheaf :
    presheafToSheaf J (Type u) ⟶
      Presheaf.freeAbelianSheaf J ⋙ sheafCompose J (forget AddCommGrpCat.{u}) where
  app P := ((sheafificationAdjunction J (Type u)).homEquiv P _).symm (toFreeAbelianSheafUnit J P)
  naturality P Q f := by
    refine ((sheafificationAdjunction J (Type u)).homEquiv P _).injective ?_
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact toFreeAbelianSheafUnit_naturality J f

/-- The comparison on sections: a map `(**Z**_P^#)|_U ⟶ F|_U` of abelian sheaves on `C / U`,
restricted along the canonical map `P^# ⟶ **Z**_P^#` of sheaves of sets, is a map
`(P^#)|_U ⟶ F|_U` of sheaves of sets. -/
def internalHomFreeAbelianSection (P : Cᵒᵖ ⥤ Type u) (F : Sheaf J AddCommGrpCat.{u}) (U : Cᵒᵖ)
    (α : (Over.forget U.unop).op ⋙ ((Presheaf.freeAbelianSheaf J).obj P).obj ⟶
      (Over.forget U.unop).op ⋙ F.obj) :
    (J.overPullback (Type u) U.unop).obj ((presheafToSheaf J (Type u)).obj P) ⟶
      (J.overPullback (Type u) U.unop).obj
        ((sheafCompose J (forget AddCommGrpCat.{u})).obj F) :=
  ⟨Functor.whiskerLeft (Over.forget U.unop).op ((toFreeAbelianSheaf J).app P).hom ≫
    Functor.whiskerRight α (forget AddCommGrpCat.{u})⟩

/-- **The comparison** `ℋom(**Z**_P^#, F) ⟶ ℋom'(P^#, F)`, a morphism of abelian sheaves: on
sections over `U` it restricts a map of abelian sheaves on `C / U` along the canonical map
`P^# ⟶ **Z**_P^#`. -/
theorem internalHomFreeAbelianSection_add (P : Cᵒᵖ ⥤ Type u) (F : Sheaf J AddCommGrpCat.{u})
    (U : Cᵒᵖ) (α β : (internalHomSheaf J ((Presheaf.freeAbelianSheaf J).obj P) F).obj.obj U) :
    sheafHomPrimeSectionsEquiv J _ F U (internalHomFreeAbelianSection J P F U (α + β)) =
      sheafHomPrimeSectionsEquiv J _ F U (internalHomFreeAbelianSection J P F U α) +
        sheafHomPrimeSectionsEquiv J _ F U (internalHomFreeAbelianSection J P F U β) := by
  refine Additive.toMul.injective (Sheaf.hom_ext (NatTrans.ext (funext fun W => ?_)))
  ext s
  refine Eq.trans ?_ (sheafHomPrimeEval_add J _ F U
    (sheafHomPrimeSectionsEquiv J _ F U (internalHomFreeAbelianSection J P F U α))
    (sheafHomPrimeSectionsEquiv J _ F U (internalHomFreeAbelianSection J P F U β)) W s).symm
  exact natTrans_add_app_apply α β W _

/-- The comparison on sections over `U`, as a homomorphism of abelian groups. -/
def internalHomFreeAbelianSectionHom (P : Cᵒᵖ ⥤ Type u) (F : Sheaf J AddCommGrpCat.{u})
    (U : Cᵒᵖ) :
    (internalHomSheaf J ((Presheaf.freeAbelianSheaf J).obj P) F).obj.obj U ⟶
      ((AbelianSheafReading.endofunctor J (SheafHomAdj.sheafHomFunctor
        ((presheafToSheaf J (Type u)).obj P))).obj F).obj.obj U :=
  ConcreteCategory.ofHom
    { toFun := fun α =>
        sheafHomPrimeSectionsEquiv J _ F U (internalHomFreeAbelianSection J P F U α)
      map_zero' := map_zero_of_map_add
        (fun α => sheafHomPrimeSectionsEquiv J _ F U (internalHomFreeAbelianSection J P F U α))
        (internalHomFreeAbelianSection_add J P F U)
      map_add' := internalHomFreeAbelianSection_add J P F U }

/-- **The comparison** `ℋom(**Z**_P^#, F) ⟶ ℋom'(P^#, F)`, a morphism of abelian sheaves: on
sections over `U` it restricts a map of abelian sheaves on `C / U` along the canonical map
`P^# ⟶ **Z**_P^#`. -/
def internalHomFreeAbelianHom (P : Cᵒᵖ ⥤ Type u) (F : Sheaf J AddCommGrpCat.{u}) :
    internalHomSheaf J ((Presheaf.freeAbelianSheaf J).obj P) F ⟶
      (AbelianSheafReading.endofunctor J
        (SheafHomAdj.sheafHomFunctor ((presheafToSheaf J (Type u)).obj P))).obj F :=
  ⟨{ app U := internalHomFreeAbelianSectionHom J P F U
     naturality := by
       intro U U' f
       apply AddCommGrpCat.hom_ext
       apply AddMonoidHom.ext
       intro α
       rfl }⟩

/-- Precomposition with an isomorphism is a bijection on hom-sets. -/
def precompEquiv {D : Type*} [Category D] {X X' : D} (i : X ≅ X') (Y : D) :
    (X ⟶ Y) ≃ (X' ⟶ Y) where
  toFun f := i.inv ≫ f
  invFun f := i.hom ≫ f
  left_inv f := by simp
  right_inv f := by simp

/-- A morphism of abelian sheaves on the localized site `C / U` is the same thing as a section of
the abelian internal hom over `U`. -/
def internalHomSectionsEquiv (A F : Sheaf J AddCommGrpCat.{u}) (U : Cᵒᵖ) :
    (internalHomSheaf J A F).obj.obj U ≃
      ((J.overPullback AddCommGrpCat.{u} U.unop).obj A ⟶
        (J.overPullback AddCommGrpCat.{u} U.unop).obj F) :=
  (Sheaf.homEquiv (J := J.over U.unop)
    (X := (J.overPullback AddCommGrpCat.{u} U.unop).obj A)
    (Y := (J.overPullback AddCommGrpCat.{u} U.unop).obj F)).symm

/-- The underlying presheaf of sets of the restriction of an abelian sheaf to a localized site is
the restriction of its underlying sheaf of sets; this records the identification of the two
hom-sets out of a presheaf of sets. -/
def restrictForgetEquiv (F : Sheaf J AddCommGrpCat.{u}) (U : Cᵒᵖ)
    (X : (Over U.unop)ᵒᵖ ⥤ Type u) :
    (X ⟶ (sheafToPresheaf (J.over U.unop) AddCommGrpCat.{u} ⋙ Presheaf.forgetAbelian).obj
        ((J.overPullback AddCommGrpCat.{u} U.unop).obj F)) ≃
      (X ⟶ (sheafToPresheaf (J.over U.unop) (Type u)).obj
        ((J.overPullback (Type u) U.unop).obj
          ((sheafCompose J (forget AddCommGrpCat.{u})).obj F))) :=
  Equiv.refl _

/-- `restrictForgetEquiv` is the identity on underlying maps. -/
theorem restrictForgetEquiv_apply (F : Sheaf J AddCommGrpCat.{u}) (U : Cᵒᵖ)
    (X : (Over U.unop)ᵒᵖ ⥤ Type u)
    (f : X ⟶ (sheafToPresheaf (J.over U.unop) AddCommGrpCat.{u} ⋙ Presheaf.forgetAbelian).obj
      ((J.overPullback AddCommGrpCat.{u} U.unop).obj F)) :
    restrictForgetEquiv J F U X f = f := rfl

/-- **The sections of the abelian internal hom out of a free abelian sheaf.** Over `U` they are
the maps `(P^#)|_U ⟶ F|_U` of sheaves of sets: the free abelian sheaf commutes with restriction
to `C / U`, so maps out of `(**Z**_P^#)|_U` are maps out of `**Z**_{P|_U}^#`; these are maps of
presheaves of sets `P|_U ⟶ F|_U`, hence maps of sheaves `(P|_U)^# ⟶ F|_U`; and sheafification
too commutes with restriction. -/
def internalHomFreeAbelianSectionEquiv (P : Cᵒᵖ ⥤ Type u) (F : Sheaf J AddCommGrpCat.{u})
    (U : Cᵒᵖ) :
    (internalHomSheaf J ((Presheaf.freeAbelianSheaf J).obj P) F).obj.obj U ≃
      ((J.overPullback (Type u) U.unop).obj ((presheafToSheaf J (Type u)).obj P) ⟶
        (J.overPullback (Type u) U.unop).obj
          ((sheafCompose J (forget AddCommGrpCat.{u})).obj F)) :=
  (internalHomSectionsEquiv J ((Presheaf.freeAbelianSheaf J).obj P) F U).trans
    ((precompEquiv ((Presheaf.freeAbelianSheafOverPullbackIso J U.unop).app P)
        ((J.overPullback AddCommGrpCat.{u} U.unop).obj F)).trans
      (((Presheaf.freeAbelianSheafAdj (J.over U.unop)).homEquiv
          ((Over.forget U.unop).op ⋙ P)
          ((J.overPullback AddCommGrpCat.{u} U.unop).obj F)).trans
        ((restrictForgetEquiv J F U ((Over.forget U.unop).op ⋙ P)).trans
        ((((sheafificationAdjunction (J.over U.unop) (Type u)).homEquiv
            ((Over.forget U.unop).op ⋙ P)
            ((J.overPullback (Type u) U.unop).obj
              ((sheafCompose J (forget AddCommGrpCat.{u})).obj F))).symm).trans
          (precompEquiv ((Presheaf.sheafificationOverPullbackIso J U.unop).app P)
            ((J.overPullback (Type u) U.unop).obj
              ((sheafCompose J (forget AddCommGrpCat.{u})).obj F))).symm))))

/-- The canonical map `P^# ⟶ **Z**_P^#` is the unit of the free-abelian-sheaf adjunction,
extended to the sheafification. -/
theorem toSheafify_toFreeAbelianSheaf (P : Cᵒᵖ ⥤ Type u) :
    toSheafify J P ≫ ((toFreeAbelianSheaf J).app P).hom = toFreeAbelianSheafUnit J P := by
  have h := ((sheafificationAdjunction J (Type u)).homEquiv P
    ((Presheaf.freeAbelianSheaf J ⋙
      sheafCompose J (forget AddCommGrpCat.{u})).obj P)).apply_symm_apply
      (toFreeAbelianSheafUnit J P)
  rw [Adjunction.homEquiv_unit] at h
  exact h

/-- **The comparison realizes the chain of bijections**: the morphism of sheaves of sets which
`internalHomFreeAbelianSection` attaches to a section of `ℋom(**Z**_P^#, F)` over `U` is the one
produced by `internalHomFreeAbelianSectionEquiv`. -/
theorem internalHomFreeAbelianSectionEquiv_eq (P : Cᵒᵖ ⥤ Type u)
    (F : Sheaf J AddCommGrpCat.{u}) (U : Cᵒᵖ)
    (α : (internalHomSheaf J ((Presheaf.freeAbelianSheaf J).obj P) F).obj.obj U) :
    internalHomFreeAbelianSectionEquiv J P F U α = internalHomFreeAbelianSection J P F U α := by
  have key : ((sheafificationAdjunction (J.over U.unop) (Type u)).homEquiv
          ((Over.forget U.unop).op ⋙ P)
          ((J.overPullback (Type u) U.unop).obj
            ((sheafCompose J (forget AddCommGrpCat.{u})).obj F))).symm
        (restrictForgetEquiv J F U ((Over.forget U.unop).op ⋙ P)
          ((Presheaf.freeAbelianSheafAdj (J.over U.unop)).homEquiv _ _
            ((Presheaf.freeAbelianSheafOverPullbackIso J U.unop).inv.app P ≫
              internalHomSectionsEquiv J ((Presheaf.freeAbelianSheaf J).obj P) F U α))) =
      ((Presheaf.sheafificationOverPullbackIso J U.unop).app P).inv ≫
        internalHomFreeAbelianSection J P F U α := by
    refine ((sheafificationAdjunction (J.over U.unop) (Type u)).homEquiv
      ((Over.forget U.unop).op ⋙ P) _).injective ?_
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      restrictForgetEquiv_apply]
    ext W x
    have h1 := congr_app_apply ((Over.forget U.unop).toSheafify_pullbackSheafificationCompatibility
      (Type u) (J.over U.unop) J P) W x
    have h2 := congr_app_apply (Presheaf.whiskerLeft_freeAbelianSheafAdj_unit_app J U.unop P) W x
    have h3 := congr_app_apply (toSheafify_toFreeAbelianSheaf J P) (op (unop W).left) x
    have inner := (h2.symm.trans h3.symm).trans
      (congrArg (fun t => (((toFreeAbelianSheaf J).app P).hom.app (op (unop W).left)) t) h1.symm)
    exact congrArg (fun t => (α.app W) t) inner
  exact (congrArg (((Presheaf.sheafificationOverPullbackIso J U.unop).app P).hom ≫ ·) key).trans
    (Iso.hom_inv_id_assoc _ _)

/-- The comparison is bijective on the sections over every object. -/
theorem internalHomFreeAbelianSectionHom_bijective (P : Cᵒᵖ ⥤ Type u)
    (F : Sheaf J AddCommGrpCat.{u}) (U : Cᵒᵖ) :
    Function.Bijective (internalHomFreeAbelianSectionHom J P F U) := by
  have h : (fun α => internalHomFreeAbelianSectionHom J P F U α) =
      (sheafHomPrimeSectionsEquiv J ((presheafToSheaf J (Type u)).obj P) F U) ∘
        (internalHomFreeAbelianSectionEquiv J P F U) := by
    funext α
    exact congrArg (fun t => sheafHomPrimeSectionsEquiv J _ F U t)
      (internalHomFreeAbelianSectionEquiv_eq J P F U α).symm
  rw [show ⇑(ConcreteCategory.hom (internalHomFreeAbelianSectionHom J P F U)) =
    (fun α => internalHomFreeAbelianSectionHom J P F U α) from rfl, h]
  exact ((sheafHomPrimeSectionsEquiv J _ F U).bijective).comp
    (internalHomFreeAbelianSectionEquiv J P F U).bijective

/-- **The comparison is an isomorphism**: it is bijective on every section group, and a morphism
of abelian sheaves which is bijective on sections is an isomorphism. -/
instance isIso_internalHomFreeAbelianHom (P : Cᵒᵖ ⥤ Type u) (F : Sheaf J AddCommGrpCat.{u}) :
    IsIso (internalHomFreeAbelianHom J P F) := by
  have h : ∀ U, IsIso (((sheafToPresheaf J AddCommGrpCat.{u}).map
      (internalHomFreeAbelianHom J P F)).app U) := fun U =>
    (ConcreteCategory.isIso_iff_bijective _).2
      (internalHomFreeAbelianSectionHom_bijective J P F U)
  have : IsIso ((sheafToPresheaf J AddCommGrpCat.{u}).map
    (internalHomFreeAbelianHom J P F)) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso (internalHomFreeAbelianHom J P F)
    (sheafToPresheaf J AddCommGrpCat.{u})

/-- Restricting a section of `SheafHom(G, F)` over `V` along `a : W ⟶ V` and evaluating it at
the tautological object of `C / W` is evaluating the original section at `a`. -/
theorem sheafHom_map_app_mk_id {G F : Sheaf J (Type u)} {V : Cᵒᵖ}
    (φ : ((SheafHomAdj.sheafHomFunctor G).obj F).obj.obj V) (a : (Over V.unop)ᵒᵖ)
    (w : G.obj.obj (op (unop a).left)) :
    ((((SheafHomAdj.sheafHomFunctor G).obj F).obj.map (unop a).hom.op) φ).hom.app
        (op (Over.mk (𝟙 (unop a).left))) w = φ.hom.app a w := by
  have hG : ((J.overPullback (Type u) V.unop).obj G).obj.map
      (Quiver.Hom.op (Over.homMk (𝟙 (unop a).left) rfl :
        Over.mk (𝟙 (unop a).left ≫ (unop a).hom) ⟶ unop a)) =
      𝟙 (G.obj.obj (op (unop a).left)) := G.obj.map_id _
  have hF : ((J.overPullback (Type u) V.unop).obj F).obj.map
      (Quiver.Hom.op (Over.homMk (𝟙 (unop a).left) rfl :
        Over.mk (𝟙 (unop a).left ≫ (unop a).hom) ⟶ unop a)) =
      𝟙 (F.obj.obj (op (unop a).left)) := F.obj.map_id _
  have hnat := φ.hom.naturality
    (Quiver.Hom.op (Over.homMk (𝟙 (unop a).left) rfl :
      Over.mk (𝟙 (unop a).left ≫ (unop a).hom) ⟶ unop a))
  rw [hG, hF] at hnat
  exact ConcreteCategory.congr_hom hnat w

/-- The hom-equivalence of the internal-hom adjunction of Stacks 0BWQ is the explicit one. -/
theorem prodSheafHomAdjunction_homEquiv (G X F : Sheaf J (Type u))
    (ψ : (prod.functor.obj G).obj X ⟶ F) :
    (SheafHomAdj.prodSheafHomAdjunction G).homEquiv X F ψ =
      SheafHomAdj.prodSheafHomEquiv' G F X ψ := by
  change (Adjunction.mkOfHomEquiv _).homEquiv X F ψ = _
  rw [Adjunction.mkOfHomEquiv_homEquiv]

/-- **The contravariant action of the internal hom on sections**: `SheafHom(g, F)` precomposes a
map `G'|_V ⟶ F|_V` with the restriction of `g` to the localized site. -/
theorem sheafHomContraMap_app_hom_app {G G' : Sheaf J (Type u)} (g : G ⟶ G')
    (F : Sheaf J (Type u)) (V : Cᵒᵖ)
    (φ : ((SheafHomAdj.sheafHomFunctor G').obj F).obj.obj V) :
    ((SheafHomAdj.sheafHomContraMap g).app F).hom.app V φ =
      (J.overPullback (Type u) V.unop).map g ≫ φ := by
  have hc : (SheafHomAdj.prodSheafHomAdjunction G').homEquiv
      ((SheafHomAdj.sheafHomFunctor G').obj F) F
      ((SheafHomAdj.prodSheafHomAdjunction G').counit.app F) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit]
    exact (SheafHomAdj.prodSheafHomAdjunction G').right_triangle_components F
  have hcc : (SheafHomAdj.prodSheafHomAdjunction G').counit.app F =
      (SheafHomAdj.prodSheafHomEquiv' G' F ((SheafHomAdj.sheafHomFunctor G').obj F)).symm
        (𝟙 ((SheafHomAdj.sheafHomFunctor G').obj F)) := by
    rw [← hc, prodSheafHomAdjunction_homEquiv, Equiv.symm_apply_apply]
  have key := SheafHomAdj.homEquiv_comp_sheafHomContraMap g F
    ((SheafHomAdj.sheafHomFunctor G').obj F)
    ((SheafHomAdj.prodSheafHomAdjunction G').counit.app F)
  rw [hc, Category.id_comp] at key
  rw [← key, prodSheafHomAdjunction_homEquiv, hcc]
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun a => ?_)
  ext t
  have hfst : (prod.fst : G' ⨯ ((SheafHomAdj.sheafHomFunctor G').obj F) ⟶ G').hom.app
        (op (unop a).left)
        (((prod.functor.map g).app ((SheafHomAdj.sheafHomFunctor G').obj F)).hom.app
          (op (unop a).left)
          (SheafHomAdj.pair G ((SheafHomAdj.sheafHomFunctor G').obj F) t
            (((SheafHomAdj.sheafHomFunctor G').obj F).obj.map (unop a).hom.op φ))) =
      g.hom.app (op (unop a).left) t := by
    refine (sheafHom_congr_app (show (prod.functor.map g).app
        ((SheafHomAdj.sheafHomFunctor G').obj F) ≫ prod.fst = prod.fst ≫ g by
      exact prod.map_fst g (𝟙 _)) _ _).trans ?_
    exact congrArg (fun z => g.hom.app (op (unop a).left) z) (SheafHomAdj.fst_pair _ _ _ _)
  have hsnd : (prod.snd : G' ⨯ ((SheafHomAdj.sheafHomFunctor G').obj F) ⟶
        ((SheafHomAdj.sheafHomFunctor G').obj F)).hom.app (op (unop a).left)
        (((prod.functor.map g).app ((SheafHomAdj.sheafHomFunctor G').obj F)).hom.app
          (op (unop a).left)
          (SheafHomAdj.pair G ((SheafHomAdj.sheafHomFunctor G').obj F) t
            (((SheafHomAdj.sheafHomFunctor G').obj F).obj.map (unop a).hom.op φ))) =
      ((SheafHomAdj.sheafHomFunctor G').obj F).obj.map (unop a).hom.op φ := by
    refine (sheafHom_congr_app (show (prod.functor.map g).app
        ((SheafHomAdj.sheafHomFunctor G').obj F) ≫ prod.snd = prod.snd by
      exact (prod.map_snd g (𝟙 _)).trans (Category.comp_id _)) _ _).trans ?_
    exact SheafHomAdj.snd_pair _ _ _ _
  have hpair : ((prod.functor.map g).app ((SheafHomAdj.sheafHomFunctor G').obj F)).hom.app
        (op (unop a).left)
        (SheafHomAdj.pair G ((SheafHomAdj.sheafHomFunctor G').obj F) t
          (((SheafHomAdj.sheafHomFunctor G').obj F).obj.map (unop a).hom.op φ)) =
      SheafHomAdj.pair G' ((SheafHomAdj.sheafHomFunctor G').obj F)
        (g.hom.app (op (unop a).left) t)
        (((SheafHomAdj.sheafHomFunctor G').obj F).obj.map (unop a).hom.op φ) := by
    exact eq_pair_of_fst_snd J _ _ _ hfst hsnd
  have hstep :
      (((SheafHomAdj.prodSheafHomEquiv' G' F ((SheafHomAdj.sheafHomFunctor G').obj F)).symm
            (𝟙 ((SheafHomAdj.sheafHomFunctor G').obj F))).hom.app (op (unop a).left))
          ((((prod.functor.map g).app ((SheafHomAdj.sheafHomFunctor G').obj F)).hom.app
              (op (unop a).left))
            (SheafHomAdj.pair G ((SheafHomAdj.sheafHomFunctor G').obj F) t
              (((SheafHomAdj.sheafHomFunctor G').obj F).obj.map (unop a).hom.op φ))) =
        φ.hom.app a (g.hom.app (op (unop a).left) t) := by
    rw [hpair]
    refine Eq.trans (SheafHomAdj.prodSheafHomEquiv'_symm_app G' (𝟙 _) _) ?_
    rw [SheafHomAdj.fst_pair, SheafHomAdj.snd_pair]
    exact sheafHom_map_app_mk_id J φ a (g.hom.app (op (unop a).left) t)
  exact hstep

/-- `P ↦ ℋom'(P^#, F)`: the primed internal hom out of the sheafification of a presheaf of sets,
read abelianly, as a contravariant functor of the presheaf. -/
def abelianSheafHomPrimeDiagram (F : Sheaf J AddCommGrpCat.{u}) :
    (Cᵒᵖ ⥤ Type u)ᵒᵖ ⥤ Sheaf J AddCommGrpCat.{u} where
  obj P := (AbelianSheafReading.endofunctor J
    (SheafHomAdj.sheafHomFunctor ((presheafToSheaf J (Type u)).obj P.unop))).obj F
  map f := (AbelianSheafReading.endofunctorNatTrans J
    (SheafHomAdj.sheafHomContraMap ((presheafToSheaf J (Type u)).map f.unop))).app F
  map_id P := by
    rw [unop_id, Functor.map_id, SheafHomAdj.sheafHomContraMap_id,
      AbelianSheafReading.endofunctorNatTrans_id]
    rfl
  map_comp f g := by
    rw [unop_comp, Functor.map_comp, SheafHomAdj.sheafHomContraMap_comp,
      AbelianSheafReading.endofunctorNatTrans_comp]
    rfl

/-- The action of `ℋom'(-^#, F)` on a morphism of presheaves of sets. -/
theorem abelianSheafHomPrimeDiagram_map (F : Sheaf J AddCommGrpCat.{u})
    {P Q : (Cᵒᵖ ⥤ Type u)ᵒᵖ} (f : P ⟶ Q) :
    (abelianSheafHomPrimeDiagram J F).map f =
      (AbelianSheafReading.endofunctorNatTrans J
        (SheafHomAdj.sheafHomContraMap ((presheafToSheaf J (Type u)).map f.unop))).app F := rfl

/-- The comparison at a fixed presheaf, as an isomorphism. -/
def internalHomFreeAbelianObjIso (P : Cᵒᵖ ⥤ Type u) (F : Sheaf J AddCommGrpCat.{u}) :
    internalHomSheaf J ((Presheaf.freeAbelianSheaf J).obj P) F ≅
      (AbelianSheafReading.endofunctor J
        (SheafHomAdj.sheafHomFunctor ((presheafToSheaf J (Type u)).obj P))).obj F where
  hom := internalHomFreeAbelianHom J P F
  inv := inv (internalHomFreeAbelianHom J P F)
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- **The comparison** `ℋom(**Z**_P^#, F) ≅ ℋom'(P^#, F)`, as an isomorphism of contravariant
functors of the presheaf of sets `P`: the abelian internal hom out of the free abelian sheaf on
`P` is the primed internal hom out of the sheafification of `P`, read abelianly. -/
def internalHomFreeAbelianIso (F : Sheaf J AddCommGrpCat.{u}) :
    (Presheaf.freeAbelianSheaf J).op ⋙ internalHomFunctor J F ≅
      abelianSheafHomPrimeDiagram J F :=
  NatIso.ofComponents (fun P => internalHomFreeAbelianObjIso J P.unop F) (by
    intro P Q f
    rw [abelianSheafHomPrimeDiagram_map]
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun U => ?_)
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro α
    have hL : Additive.toMul (((((Presheaf.freeAbelianSheaf J).op ⋙
            internalHomFunctor J F).map f ≫
          (internalHomFreeAbelianObjIso J Q.unop F).hom).hom.app U) α) =
        internalHomFreeAbelianSection J Q.unop F U
          ((((Presheaf.freeAbelianSheaf J).op ⋙ internalHomFunctor J F).map f).hom.app U α) := rfl
    have hR : Additive.toMul ((((internalHomFreeAbelianObjIso J P.unop F).hom ≫
            (AbelianSheafReading.endofunctorNatTrans J (SheafHomAdj.sheafHomContraMap
              ((presheafToSheaf J (Type u)).map f.unop))).app F).hom.app U) α) =
        ((SheafHomAdj.sheafHomContraMap ((presheafToSheaf J (Type u)).map f.unop)).app
            ((sheafCompose J (forget AddCommGrpCat.{u})).obj F)).hom.app U
          (internalHomFreeAbelianSection J P.unop F U α) := rfl
    refine Additive.toMul.injective (hL.trans (Eq.trans ?_ hR.symm))
    refine Eq.trans ?_ (sheafHomContraMap_app_hom_app J
      ((presheafToSheaf J (Type u)).map f.unop)
      ((sheafCompose J (forget AddCommGrpCat.{u})).obj F) U
      (internalHomFreeAbelianSection J P.unop F U α)).symm
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun W => ?_)
    ext s
    exact congrArg (fun t => (α.app W) t)
      (ConcreteCategory.congr_hom (NatTrans.congr_app
        (congrArg (fun m : (presheafToSheaf J (Type u)).obj Q.unop ⟶
          (Presheaf.freeAbelianSheaf J ⋙
            sheafCompose J (forget AddCommGrpCat.{u})).obj P.unop => m.hom)
          ((toFreeAbelianSheaf J).naturality f.unop)) (op (unop W).left)) s).symm)

end SheafHomPrime

end CategoryTheory

end
