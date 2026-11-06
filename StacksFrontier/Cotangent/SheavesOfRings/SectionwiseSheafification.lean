module

public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.SheavesOfRings.SectionsComparisonNaturality

/-!
# The cotangent complex of sheaves of rings is the sheafification of the sectionwise one

Let `A ⟶ B` be a homomorphism of sheaves of commutative rings on a site. Over every object `U`
there is the canonical map `L_{B(U)/A(U)} ⟶ L_{B/A}(U)` of
`CategoryTheory.Sheaf.sectionsCotangentComplexComparison`, and these maps are compatible with the
restriction maps (`CategoryTheory.Sheaf.sectionsCotangentComplexComparison_restriction`). Then
`L_{B/A}` is, degreewise, the sheafification of the rule `U ↦ L_{B(U)/A(U)}` along these canonical
maps.

## Main definitions

* `CategoryTheory.Sheaf.sectionwiseResolutionPresheaf`: the presheaf of rings
  `U ↦ P'_n(U)`, the degree-`n` term of the standard resolution of `A(U) → B(U)`.
* `CategoryTheory.Sheaf.sectionwiseResolutionComparison`: the comparison of that presheaf of
  rings with the degree-`n` term of the standard resolution of `A ⟶ B`.
* `CategoryTheory.Sheaf.sectionwiseCotangentTerm`: the presheaf of `B`-modules
  `U ↦ L^j_{B(U)/A(U)}`, and `CategoryTheory.Sheaf.sectionwiseCotangentTermComparison` its
  canonical map to the degree-`j` term of `L_{B/A}`.

## Main results

* `CategoryTheory.Sheaf.W_sectionwiseResolutionComparison`: the comparison of standard resolutions
  is inverted by sheafification: the degree-`n` term of the standard resolution of `A ⟶ B` is the
  sheafification of `U ↦ P'_n(U)`.
* `CategoryTheory.Sheaf.isIso_sheafify_sectionwiseCotangentTermComparison`: in every degree `j` the
  term of `L_{B/A}` is the sheafification of the presheaf of `B`-modules `U ↦ L^j_{B(U)/A(U)}`
  along the canonical maps.
* `CategoryTheory.Sheaf.W_toPresheaf_sectionwiseCotangentTermComparison`: the same statement on
  underlying presheaves of abelian groups: the canonical map from the presheaf
  `CategoryTheory.Sheaf.sectionwiseCotangentComplex` to the underlying presheaf of `L_{B/A}` is, in
  every degree, inverted by sheafification.
* `CategoryTheory.Sheaf.sheafifiedSectionwiseCotangentComplexIso`: the sheafification of the
  presheaf of complexes `U ↦ L_{B(U)/A(U)}` is `L_{B/A}`, along the canonical maps.
* `CategoryTheory.Sheaf.quasiIso_of_sectionwise`: a map of complexes of sheaves of abelian groups
  is a quasi-isomorphism as soon as it is covered, through maps inverted by sheafification, by a
  sectionwise quasi-isomorphism of complexes of presheaves.

## References

* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08SW](https://stacks.math.columbia.edu/tag/08SW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory.Sheaf

universe u v w t

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-! ## Sheafification of presheaves of commutative rings -/

/-- On a small site the forgetful functor from commutative rings preserves sheafification. -/
private theorem preservesSheafification_forget_commRingCat_small {D : Type w} [SmallCategory D]
    (K : GrothendieckTopology D) : K.PreservesSheafification (forget CommRingCat.{w}) :=
  inferInstance

/-- On a small site sheafification of presheaves of commutative rings inverts exactly the
locally bijective maps. -/
private theorem wEqualsLocallyBijective_commRingCat_small {D : Type w} [SmallCategory D]
    (K : GrothendieckTopology D) : K.WEqualsLocallyBijective CommRingCat.{w} :=
  inferInstance

/-- The forgetful functor from commutative rings preserves sheafification, on a site whose
universes are contained in that of the sections. -/
theorem preservesSheafification_forget_commRingCat :
    J.PreservesSheafification (forget CommRingCat.{max u v w}) := by
  have := preservesSheafification_forget_commRingCat_small
    ((equivSmallModel.{max u v w} C).inverse.inducedTopology J)
  exact GrothendieckTopology.PreservesSheafification.transport J
    ((equivSmallModel.{max u v w} C).inverse.inducedTopology J)
    (equivSmallModel.{max u v w} C).inverse _ _

/-- Sheafification of presheaves of commutative rings inverts exactly the locally bijective
maps, on a site whose universes are contained in that of the sections. -/
theorem wEqualsLocallyBijective_commRingCat :
    J.WEqualsLocallyBijective CommRingCat.{max u v w} := by
  have := wEqualsLocallyBijective_commRingCat_small
    ((equivSmallModel.{max u v w} C).inverse.inducedTopology J)
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, _, u, _, max u v w} J

attribute [local instance] preservesSheafification_forget_commRingCat
  wEqualsLocallyBijective_commRingCat

/-! ## The universal property of the free algebra sheaf -/

section Free

variable (A : Sheaf J CommRingCat.{max u v w}) (E : Sheaf J (Type (max u v w)))

/-- A morphism of sheaves of rings out of the free `A`-algebra sheaf on `E` is a morphism out of
`A` together with a morphism of sheaves of sets out of `E`. -/
noncomputable def freeAlgebraSheafHomEquiv (T : Sheaf J CommRingCat.{max u v w}) :
    (((freeAlgebraSheaf.{v, u, w} J A).obj E).right ⟶ T) ≃
      (A ⟶ T) × (E ⟶ (sheafForget J).obj T) where
  toFun s := ⟨((freeAlgebraSheaf.{v, u, w} J A).obj E).hom ≫ s,
    (freeAlgebraSheafAdjunction.{v, u, w} J A).unit.app E ≫ (sheafForget J).map s⟩
  invFun p := ((freeAlgebraSheafAdjunction.{v, u, w} J A).homEquiv E (Under.mk p.1)).symm
    p.2 |>.right
  left_inv s := by
    let s' : (freeAlgebraSheaf.{v, u, w} J A).obj E ⟶
        Under.mk (((freeAlgebraSheaf.{v, u, w} J A).obj E).hom ≫ s) := Under.homMk s
    have h := ((freeAlgebraSheafAdjunction.{v, u, w} J A).homEquiv E
      (Under.mk (((freeAlgebraSheaf.{v, u, w} J A).obj E).hom ≫ s))).symm_apply_apply s'
    rw [Adjunction.homEquiv_unit] at h
    exact congrArg Under.Hom.right h
  right_inv p := by
    apply Prod.ext
    · exact Under.w _
    · have h := ((freeAlgebraSheafAdjunction.{v, u, w} J A).homEquiv E
        (Under.mk p.1)).apply_symm_apply p.2
      rw [Adjunction.homEquiv_unit] at h
      exact h

/-- A map of presheaves of rings into the free `A`-algebra sheaf on `E` is inverted by
sheafification as soon as its source is, sectionwise and compatibly, freely generated over `A`
by a presheaf of sets which maps to `E` by a map inverted by sheafification, the generators
going to the generators. -/
theorem W_of_freeAlgebraSheaf
    (P : Cᵒᵖ ⥤ Type (max u v w)) (r : P ⟶ E.obj) (hr : J.W r)
    (Q : Cᵒᵖ ⥤ CommRingCat.{max u v w}) (b : A.obj ⟶ Q)
    (x : P ⟶ Q ⋙ forget _) (c : Q ⟶ ((freeAlgebraSheaf.{v, u, w} J A).obj E).right.obj)
    (hb : b ≫ c = ((freeAlgebraSheaf.{v, u, w} J A).obj E).hom.hom)
    (hx : x ≫ Functor.whiskerRight c (forget _) =
      r ≫ ((freeAlgebraSheafAdjunction.{v, u, w} J A).unit.app E).hom)
    (hQ : ∀ T : Cᵒᵖ ⥤ CommRingCat.{max u v w}, Function.Bijective
      (fun g : Q ⟶ T => (b ≫ g, x ≫ Functor.whiskerRight g (forget _)))) : J.W c := by
  intro T hT
  let T' : Sheaf J CommRingCat.{max u v w} := ⟨T, hT⟩
  let e : (((freeAlgebraSheaf.{v, u, w} J A).obj E).right.obj ⟶ T) ≃
      (A.obj ⟶ T) × (P ⟶ T ⋙ forget _) :=
    Sheaf.homEquiv.symm.trans ((freeAlgebraSheafHomEquiv J A E T').trans
      (Equiv.prodCongr Sheaf.homEquiv (Sheaf.homEquiv.trans
        (ObjectProperty.isLocal.homEquiv hr _ ((sheafForget J).obj T').property))))
  have he (g : ((freeAlgebraSheaf.{v, u, w} J A).obj E).right.obj ⟶ T) :
      e g = (b ≫ (c ≫ g), x ≫ Functor.whiskerRight (c ≫ g) (forget _)) := by
    apply Prod.ext
    · show ((freeAlgebraSheaf.{v, u, w} J A).obj E).hom.hom ≫ g = _
      rw [← hb, Category.assoc]
    · ext U s
      show (g.app U) ((((freeAlgebraSheafAdjunction.{v, u, w} J A).unit.app E).hom.app U)
          (r.app U s)) = (g.app U) (c.app U (x.app U s))
      have h : (c.app U) ((x.app U) s) =
          (((freeAlgebraSheafAdjunction.{v, u, w} J A).unit.app E).hom.app U) (r.app U s) :=
        ConcreteCategory.congr_hom (NatTrans.congr_app hx U) s
      exact congrArg (g.app U) h.symm
  refine ⟨?_, ?_⟩
  · intro g h eq
    apply e.injective
    exact (he g).trans
      ((congrArg (fun k => (b ≫ k, x ≫ Functor.whiskerRight k (forget _))) eq).trans
        (he h).symm)
  · intro g
    refine ⟨e.symm (b ≫ g, x ≫ Functor.whiskerRight g (forget _)), ?_⟩
    exact (hQ T).injective ((he _).symm.trans (e.apply_symm_apply _))

end Free

/-- A presheaf of rings which is, sectionwise, freely generated over `R` by a presheaf of sets
`P`, is freely generated over `R` by `P` as a presheaf: maps out of it into any presheaf of
rings are maps out of `R` together with maps of presheaves of sets out of `P`. -/
theorem bijective_presheafHom_of_sectionwise
    (R Q : Cᵒᵖ ⥤ CommRingCat.{max u v w}) (P : Cᵒᵖ ⥤ Type (max u v w))
    (b : R ⟶ Q) (x : P ⟶ Q ⋙ forget _)
    (hQ : ∀ U (T : CommRingCat.{max u v w}), Function.Bijective
      (fun g : Q.obj U ⟶ T => (b.app U ≫ g, x.app U ≫ (forget _).map g)))
    (T : Cᵒᵖ ⥤ CommRingCat.{max u v w}) : Function.Bijective
      (fun g : Q ⟶ T => (b ≫ g, x ≫ Functor.whiskerRight g (forget _))) := by
  constructor
  · intro g h eq
    apply NatTrans.ext
    funext U
    exact (hQ U (T.obj U)).injective
      (Prod.ext (NatTrans.congr_app (Prod.mk.inj eq).1 U) (NatTrans.congr_app (Prod.mk.inj eq).2 U))
  · intro p
    choose g hg using fun U => (hQ U (T.obj U)).surjective (p.1.app U, p.2.app U)
    have hg₁ (U) : b.app U ≫ g U = p.1.app U := (Prod.mk.inj (hg U)).1
    have hg₂ (U) : x.app U ≫ (forget _).map (g U) = p.2.app U := (Prod.mk.inj (hg U)).2
    have hs (U) (s) : g U (x.app U s) = p.2.app U s := ConcreteCategory.congr_hom (hg₂ U) s
    let φ : Q ⟶ T :=
      { app := g
        naturality := by
          intro U V k
          apply (hQ U (T.obj V)).injective
          apply Prod.ext
          · show b.app U ≫ Q.map k ≫ g V = b.app U ≫ g U ≫ T.map k
            rw [← b.naturality_assoc, hg₁, ← Category.assoc, hg₁, p.1.naturality]
          · ext s
            show g V (Q.map k (x.app U s)) = T.map k (g U (x.app U s))
            have hx : Q.map k (x.app U s) = x.app V (P.map k s) :=
              (ConcreteCategory.congr_hom (x.naturality k) s).symm
            rw [hx, hs, hs]
            exact ConcreteCategory.congr_hom (p.2.naturality k) s }
    exact ⟨φ, Prod.ext (NatTrans.ext (funext hg₁)) (NatTrans.ext (funext hg₂))⟩

/-- Ring maps out of a polynomial algebra are maps out of the coefficient ring together with maps
out of the set of variables. -/
theorem bijective_mvPolynomialHom {R : Type t} [CommRing R]
    {σ : Type t} (T : CommRingCat.{t}) : Function.Bijective
      (fun g : CommRingCat.of (MvPolynomial σ R) ⟶ T =>
        (CommRingCat.ofHom (algebraMap R (MvPolynomial σ R)) ≫ g,
          ((↾fun i : σ => g (MvPolynomial.X i)) : (σ ⟶ (forget _).obj T)))) := by
  constructor
  · intro g h eq
    exact CommRingCat.hom_ext <| MvPolynomial.ringHom_ext
      (ConcreteCategory.congr_hom (Prod.mk.inj eq).1)
      (ConcreteCategory.congr_hom (Prod.mk.inj eq).2)
  · intro p
    refine ⟨CommRingCat.ofHom (MvPolynomial.eval₂Hom p.1.hom p.2), ?_⟩
    apply Prod.ext
    · ext r
      exact MvPolynomial.eval₂_C _ _ _
    · ext i
      exact MvPolynomial.eval₂_X _ _ _

/-! ## The sectionwise tower of iterated polynomial algebras -/

section Tower

variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-- The presheaf of rings `U ↦ A(U)[A(U)[⋯[B(U)]⋯]]` of stage `n` of the tower of iterated
polynomial algebras of the ring maps `A(U) → B(U)`, with the tower maps of the restriction
squares as restriction maps. Its stage `n + 1` is the degree-`n` term of the standard resolution
of `A(U) → B(U)`. -/
noncomputable def sectionwiseTowerPresheaf (n : ℕ) : Cᵒᵖ ⥤ CommRingCat.{max u v w} where
  obj U := CommRingCat.of (CommAlgCat.standardTower.{max u v w, max u v w} (A.obj.obj U)
    (sectionsAlgebra J f U) n)
  map g := CommRingCat.ofHom (CommAlgCat.standardTowerMap.{max u v w, max u v w, max u v w}
    (sectionsRestrictionSquare J f g) n)
  map_id U := by
    apply CommRingCat.hom_ext
    change CommAlgCat.standardTowerMap (sectionsRestrictionSquare J f (𝟙 U)) n = _
    rw [sectionsRestrictionSquare_id, CommAlgCat.standardTowerMap_id]
    rfl
  map_comp g h := by
    apply CommRingCat.hom_ext
    change CommAlgCat.standardTowerMap (sectionsRestrictionSquare J f (g ≫ h)) n = _
    rw [sectionsRestrictionSquare_comp, CommAlgCat.standardTowerMap_comp]
    rfl

/-- The structure map `A ⟶ U ↦ A(U)[⋯]` into a positive stage of the sectionwise tower. -/
noncomputable def sectionwiseTowerBase (n : ℕ) : A.obj ⟶ sectionwiseTowerPresheaf J f (n + 1) where
  app U := CommRingCat.ofHom (algebraMap (A.obj.obj U)
    (CommAlgCat.standardTower.{max u v w, max u v w} (A.obj.obj U) (sectionsAlgebra J f U)
      (n + 1)))
  naturality {U V} g := by
    ext a
    exact (CommAlgCat.standardTowerMap_algebraMap.{max u v w, max u v w, max u v w}
      (sectionsRestrictionSquare J f g) (n + 1) a).symm

/-- The variables of stage `n + 1` of the sectionwise tower, indexed by the elements of stage
`n`. -/
noncomputable def sectionwiseTowerVariable (n : ℕ) :
    sectionwiseTowerPresheaf J f n ⋙ forget _ ⟶
      sectionwiseTowerPresheaf J f (n + 1) ⋙ forget _ where
  app U := ↾CommAlgCat.standardTowerX.{max u v w, max u v w} (A.obj.obj U)
    (sectionsAlgebra J f U) n
  naturality {U V} g := by
    ext q
    exact (CommAlgCat.standardTowerMap_standardTowerX.{max u v w, max u v w, max u v w}
      (sectionsRestrictionSquare J f g) n q).symm

/-- The comparison of the sectionwise tower with the iterates of the free-algebra-sheaf comonad at
`B`: over every `U` it is the iterated comonad comparison. -/
noncomputable def sectionwiseTowerComparison (n : ℕ) :
    sectionwiseTowerPresheaf J f n ⟶
      (((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
        Under A ⥤ Under A).iterate n).obj (Under.mk f) |>.right.obj where
  app U := CommRingCat.ofHom
    ((Functor.iterateLaxHom (sectionsComonadLax J U) n).app (Under.mk f)).hom.toRingHom
  naturality {U V} g := by
    ext q
    exact (iterateSectionsComonadLax_restriction J f g n q).symm

/-- The comparison of the sectionwise tower is compatible with the structure maps from `A`. -/
theorem sectionwiseTowerBase_comp_comparison (n : ℕ) :
    sectionwiseTowerBase J f n ≫ sectionwiseTowerComparison J f (n + 1) =
      ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
        Under A ⥤ Under A).iterate (n + 1)).obj (Under.mk f)).hom.hom := by
  ext U a
  exact ((Functor.iterateLaxHom (sectionsComonadLax J U) (n + 1)).app
    (Under.mk f)).hom.commutes a

/-- **The comparison of the sectionwise tower sends variables to variables**: the variable `[q]`
of stage `n + 1` goes to the image under the unit of the free-algebra-sheaf adjunction of the
comparison of `q`. -/
theorem sectionwiseTowerVariable_comp_comparison (n : ℕ) :
    sectionwiseTowerVariable J f n ≫
        Functor.whiskerRight (sectionwiseTowerComparison J f (n + 1)) (forget _) =
      Functor.whiskerRight (sectionwiseTowerComparison J f n) (forget _) ≫
        ((freeAlgebraSheafAdjunction.{v, u, w} J A).unit.app
          ((forgetAlgebraSheaf.{v, u, w} J A).obj
            ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
              Under A ⥤ Under A).iterate n).obj (Under.mk f)))).hom := by
  ext U q
  refine (iterateSectionsComonadLax_succ_apply J f U n
    (CommAlgCat.standardTowerX.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U) n q)).trans ?_
  refine (congrArg (fun z => ((sectionsComonadLax J U).app
      ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
        Under A ⥤ Under A).iterate n).obj (Under.mk f))).hom z)
    (CommAlgCat.polynomialComonad_map_X.{max u v w, max u v w} (A.obj.obj U)
      ((Functor.iterateLaxHom (sectionsComonadLax J U) n).app (Under.mk f)) q)).trans ?_
  exact sectionsComonadLax_variable J U _ _

/-- At stage zero the comparison of the sectionwise tower is invertible: both sides are `B`. -/
instance isIso_sectionwiseTowerComparison_zero : IsIso (sectionwiseTowerComparison J f 0) := by
  have : ∀ U, IsIso ((sectionwiseTowerComparison J f 0).app U) := fun U =>
    ⟨CommRingCat.ofHom (RingHom.id _), by ext; rfl, by ext; rfl⟩
  exact NatIso.isIso_of_isIso_app _

/-- Stage `n + 1` of the sectionwise tower is freely generated over `A` by stage `n`, as a
presheaf of rings. -/
theorem bijective_sectionwiseTowerPresheaf_hom (n : ℕ) (T : Cᵒᵖ ⥤ CommRingCat.{max u v w}) :
    Function.Bijective (fun g : sectionwiseTowerPresheaf J f (n + 1) ⟶ T =>
      (sectionwiseTowerBase J f n ≫ g,
        sectionwiseTowerVariable J f n ≫ Functor.whiskerRight g (forget _))) := by
  refine bijective_presheafHom_of_sectionwise _ _ _ _ _ (fun U T' => ?_) T
  exact bijective_mvPolynomialHom T'

/-- **The comparison of the sectionwise tower is inverted by sheafification**: stage `n` of the
iterated free-algebra-sheaf comonad at `B` is the sheafification of the presheaf
`U ↦ A(U)[⋯[B(U)]⋯]`. -/
theorem W_sectionwiseTowerComparison (n : ℕ) : J.W (sectionwiseTowerComparison J f n) := by
  induction n with
  | zero => exact ObjectProperty.isLocal_of_isIso _ _
  | succ n ih =>
    have hr := J.W_of_preservesSheafification (forget _) _ ih
    exact W_of_freeAlgebraSheaf J A _ _ _ hr _ _ _ _
      (sectionwiseTowerBase_comp_comparison J f n)
      (sectionwiseTowerVariable_comp_comparison J f n)
      (bijective_sectionwiseTowerPresheaf_hom J f n)

end Tower

/-! ## The sectionwise standard resolution -/

section Resolution

variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-- The presheaf of rings `U ↦ P'_n(U)`, the degree-`n` term of the standard resolution of the
ring map `A(U) → B(U)`, with the maps of standard resolutions induced by the restriction squares
as restriction maps. -/
noncomputable def sectionwiseResolutionPresheaf (n : SimplexCategoryᵒᵖ) :
    Cᵒᵖ ⥤ CommRingCat.{max u v w} where
  obj U := CommRingCat.of ((CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
    (sectionsAlgebra J f U)).left.obj n)
  map g := CommRingCat.ofHom ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
    (sectionsRestrictionSquare J f g)).resolution n)
  map_id U := by
    apply CommRingCat.hom_ext
    change (CommAlgCat.squareFunctoriality (sectionsRestrictionSquare J f (𝟙 U))).resolution n = _
    rw [sectionsRestrictionSquare_id, CommAlgCat.squareFunctoriality_resolution_id]
    rfl
  map_comp g h := by
    apply CommRingCat.hom_ext
    change (CommAlgCat.squareFunctoriality
      (sectionsRestrictionSquare J f (g ≫ h))).resolution n = _
    rw [sectionsRestrictionSquare_comp, CommAlgCat.squareFunctoriality_resolution_comp]
    rfl

/-- The structure map `A ⟶ (U ↦ P'_n(U))`. -/
noncomputable def sectionwiseResolutionBase (n : SimplexCategoryᵒᵖ) :
    A.obj ⟶ sectionwiseResolutionPresheaf J f n where
  app U := CommRingCat.ofHom (algebraMap (A.obj.obj U)
    ((CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj n))
  naturality {U V} g := by
    ext a
    exact ((CommAlgCat.squareFunctoriality.{max u v w, max u v w, max u v w}
      (sectionsRestrictionSquare J f g)).resolution_algebraMap n a).symm

/-- **The comparison of standard resolutions, as a map of presheaves of rings**: over every `U` it
is the comparison `P'_n(U) ⟶ P_n(U)` of the degree-`n` term of the standard resolution of
`A(U) → B(U)` with the sections over `U` of the degree-`n` term of the standard resolution of
`A ⟶ B`. -/
noncomputable def sectionwiseResolutionComparison (n : SimplexCategoryᵒᵖ) :
    sectionwiseResolutionPresheaf J f n ⟶ (resolutionTerm J f n).obj where
  app U := CommRingCat.ofHom ((resolutionSectionsComparison J f U).app n).hom.toRingHom
  naturality {U V} g := by
    ext p
    exact (resolutionTerm_map_resolutionSectionsComparison J f g n p).symm

/-- The comparison of standard resolutions is compatible with the structure maps from `A`. -/
theorem sectionwiseResolutionBase_comp_comparison (n : SimplexCategoryᵒᵖ) :
    sectionwiseResolutionBase J f n ≫ sectionwiseResolutionComparison J f n =
      (resolutionBase J f n).hom := by
  ext U a
  exact ((resolutionSectionsComparison J f U).app n).hom.commutes a

/-- The degree-`n` term of the sectionwise standard resolution is stage `n + 1` of the
sectionwise tower. -/
noncomputable def sectionwiseResolutionTowerIso (n : ℕ) :
    sectionwiseResolutionPresheaf J f (op ⦋n⦌) ≅ sectionwiseTowerPresheaf J f (n + 1) :=
  NatIso.ofComponents (fun U => (forget₂ (CommAlgCat.{max u v w} (A.obj.obj U))
      CommRingCat.{max u v w}).mapIso (eqToIso
        (CommAlgCat.standardResolution_obj_eq_standardTower.{max u v w, max u v w}
          (A.obj.obj U) (sectionsAlgebra J f U) n))) (by
    intro U V g
    ext p
    change eqToHom (CommAlgCat.standardResolution_obj_eq_standardTower.{max u v w, max u v w}
        (A.obj.obj V) (sectionsAlgebra J f V) n)
        (CommAlgCat.standardResolutionSquareMap.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f g) (op ⦋n⦌) p) = _
    exact (congrArg (eqToHom (CommAlgCat.standardResolution_obj_eq_standardTower.{max u v w,
        max u v w} (A.obj.obj V) (sectionsAlgebra J f V) n))
      (CommAlgCat.standardResolutionSquareMap_apply _ n p)).trans
        (CommAlgCat.eqToHom_eqToHom_apply _ _ _))

/-- The degree-`n` term of the standard resolution of `A ⟶ B`, as a presheaf of rings, is the
`(n + 1)`-st iterate of the free-algebra-sheaf comonad at `B`. -/
noncomputable def resolutionTermIterateIso (n : ℕ) :
    ((((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
        Under A ⥤ Under A).iterate (n + 1)).obj (Under.mk f)).right.obj ≅
      (resolutionTerm J f (op ⦋n⦌)).obj :=
  (Under.forget A ⋙ sheafToPresheaf J _).mapIso
    (eqToIso (standardResolution_obj.{v, u, w} J f n).symm)

/-- The comparison of standard resolutions is the comparison of the sectionwise tower, read
through the identifications of both terms with stages of the towers. -/
theorem sectionwiseResolutionComparison_eq (n : ℕ) :
    sectionwiseResolutionComparison J f (op ⦋n⦌) =
      (sectionwiseResolutionTowerIso J f n).hom ≫ sectionwiseTowerComparison J f (n + 1) ≫
        (resolutionTermIterateIso J f n).hom := by
  ext U p
  rfl

/-- **The degree-`n` term of the standard resolution of `A ⟶ B` is the sheafification of
`U ↦ P'_n(U)`**: the comparison of standard resolutions is inverted by sheafification. -/
theorem W_sectionwiseResolutionComparison (n : SimplexCategoryᵒᵖ) :
    J.W (sectionwiseResolutionComparison J f n) := by
  obtain ⟨⟨n⟩⟩ := n
  rw [sectionwiseResolutionComparison_eq]
  exact MorphismProperty.comp_mem _ _ _ (ObjectProperty.isLocal_of_isIso _ _)
    (MorphismProperty.comp_mem _ _ _ (W_sectionwiseTowerComparison J f (n + 1))
      (ObjectProperty.isLocal_of_isIso _ _))

end Resolution

/-! ## Derivations into a sheaf extend along a map inverted by sheafification -/

section Derivations

attribute [local instance] moduleOfSections

/-- Two families of maps of sections into a sheaf of sets, natural in the site variable, agree as
soon as they agree on the image of a locally surjective map. -/
theorem eq_of_isLocallySurjective_binary {P F : Cᵒᵖ ⥤ Type (max u v w)} (c : P ⟶ F)
    [Presheaf.IsLocallySurjective J c] (M : Sheaf J (Type (max u v w)))
    (a b : ∀ U, F.obj U → F.obj U → M.obj.obj U)
    (ha : ∀ {U V} (g : U ⟶ V) x y, M.obj.map g (a U x y) = a V (F.map g x) (F.map g y))
    (hb : ∀ {U V} (g : U ⟶ V) x y, M.obj.map g (b U x y) = b V (F.map g x) (F.map g y))
    (h : ∀ U x y, a U (c.app U x) (c.app U y) = b U (c.app U x) (c.app U y))
    (U : Cᵒᵖ) (x y : F.obj U) : a U x y = b U x y := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 M.property).isSeparated _
    (J.intersection_covering (Presheaf.imageSieve_mem J c x)
      (Presheaf.imageSieve_mem J c y))).ext
  rintro V g ⟨⟨x', hx⟩, ⟨y', hy⟩⟩
  rw [ha, hb, ← hx, ← hy, h]

variable {A R : Sheaf J CommRingCat.{max u v w}} (a : A ⟶ R)

/-- **Derivations into a sheaf extend along a map inverted by sheafification.** Let
`c : Q ⟶ R` be a map from a presheaf of rings to a sheaf of rings, inverted by sheafification and
compatible with structure maps from `A`. Every `A`-derivation of `Q` into a sheaf of `R`-modules
extends to an `A`-derivation of `R`. -/
theorem exists_derivation_extension (Q : Cᵒᵖ ⥤ CommRingCat.{max u v w}) (b : A.obj ⟶ Q)
    (c : Q ⟶ R.obj) (hbc : b ≫ c = a.hom) (hc : J.W c)
    (M : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} R))
    (d : PresheafOfModulesOfCommRing.Derivation' ((PresheafOfModules.restrictScalars
      (Functor.whiskerRight c (forget₂ CommRingCat RingCat))).obj M.val) b) :
    ∃ D : PresheafOfModulesOfCommRing.Derivation' M.val a.hom, ∀ U q, D.d (c.app U q) = d.d q := by
  have : Presheaf.IsLocallySurjective J c := hc.isLocallySurjective
  let dAb : Q ⋙ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) ⟶
      M.val.presheaf :=
    { app U := AddCommGrpCat.ofHom d.d
      naturality {U V} g := by ext q; exact d.d_map g q }
  let cAb := Functor.whiskerRight c (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
  have hcAb : J.W cAb := by
    have := hc.isLocallyInjective
    rw [J.W_iff_isLocallyBijective]
    constructor
    · exact (Presheaf.isLocallyInjective_forget_iff J cAb).mp
        ((Presheaf.isLocallyInjective_forget_iff J c).mpr inferInstance)
    · exact (Presheaf.isLocallySurjective_iff_whisker_forget J cAb).mpr
        ((Presheaf.isLocallySurjective_iff_whisker_forget J c).mp inferInstance)
  obtain ⟨e, he⟩ := (hcAb M.val.presheaf M.isSheaf).surjective dAb
  let Dadd (U) : R.obj.obj U →+ M.val.obj U := (e.app U).hom
  have heq U q : Dadd U (c.app U q) = d.d q :=
    ConcreteCategory.congr_hom (NatTrans.congr_app he U) q
  have enat {U V} (g : U ⟶ V) (x : R.obj.obj U) :
      M.val.map g (Dadd U x) = Dadd V (R.obj.map g x) :=
    (ConcreteCategory.congr_hom (e.naturality g) x).symm
  refine ⟨{ d := fun {U} => Dadd U
            d_map := fun g x => (enat g x).symm
            d_app := ?_
            d_mul := ?_ }, heq⟩
  · intro U x y
    let MT : Sheaf J (Type (max u v w)) := (sheafCompose J (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf _).obj M)
    let ct := Functor.whiskerRight c (forget CommRingCat)
    have : Presheaf.IsLocallySurjective J ct :=
      (Presheaf.isLocallySurjective_iff_whisker_forget J c).mp inferInstance
    refine eq_of_isLocallySurjective_binary J ct MT
      (fun U (x y : R.obj.obj U) => Dadd U (x * y))
      (fun U (x y : R.obj.obj U) => x • Dadd U y + y • Dadd U x)
      ?_ ?_ ?_ U x y
    · rintro U V g (x : R.obj.obj U) (y : R.obj.obj U)
      show M.val.map g (Dadd U (x * y)) = Dadd V (_ * _)
      rw [enat, map_mul]
      rfl
    · rintro U V g (x : R.obj.obj U) (y : R.obj.obj U)
      have e₁ := M.val.map_smul g x (Dadd U y)
      have e₂ := M.val.map_smul g y (Dadd U x)
      rw [enat] at e₁ e₂
      exact ((M.val.map g).hom.map_add _ _).trans (congrArg₂ (· + ·) e₁ e₂)
    · intro U q r
      show Dadd U (c.app U q * c.app U r) =
        c.app U q • Dadd U (c.app U r) + c.app U r • Dadd U (c.app U q)
      rw [← map_mul, heq, heq, heq]
      exact d.d_mul q r
  · intro U x
    rw [← hbc]
    exact (heq U (b.app U x)).trans (d.d_app x)

/-- **Derivations into a sheaf are determined on the image of a map inverted by
sheafification.** -/
theorem derivation_ext_of_W (Q : Cᵒᵖ ⥤ CommRingCat.{max u v w}) (c : Q ⟶ R.obj) (hc : J.W c)
    (M : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} R))
    (D E : PresheafOfModulesOfCommRing.Derivation' M.val a.hom) (h : ∀ U q, D.d (c.app U q) = E.d (c.app U q)) :
    D = E := by
  let MT : Sheaf J (Type (max u v w)) := (sheafCompose J (forget AddCommGrpCat)).obj
    ((SheafOfModules.toSheaf _).obj M)
  have hct := J.W_of_preservesSheafification (forget CommRingCat) _ hc
  let dT (D : PresheafOfModulesOfCommRing.Derivation' M.val a.hom) : R.obj ⋙ forget _ ⟶ MT.obj :=
    { app U := ↾D.d
      naturality {U V} g := by ext x; exact D.d_map g x }
  have hDE : dT D = dT E := (hct MT.obj MT.property).injective (by
    ext U q
    exact h U q)
  ext U x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app hDE U) x

end Derivations

/-! ## The terms of `L_{B/A}` are sheafifications -/

section Terms

variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-- Two module maps out of a term of the cotangent complex of `A(U) → B(U)` agree as soon as they
agree on the pure differentials `1 ⊗ d p`. -/
theorem sectionsCotangentComplex_hom_ext (U : Cᵒᵖ) (n : ℕ)
    {N : ModuleCat.{max u v w} (sectionsAlgebra J f U)}
    (α β : (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).X (-(n : ℤ)) ⟶ N)
    (h : ∀ p, α (sectionsCotangentDifferential' J f U n p) =
      β (sectionsCotangentDifferential' J f U n p)) : α = β := by
  refine (cancel_epi (CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w}
    (A.obj.obj U) (sectionsAlgebra J f U) n).inv).mp ?_
  exact CommAlgCat.cotangentTerm_hom_ext.{max u v w, max u v w} _ _ _ _ _ h

/-- The presheaf of `B`-modules `U ↦ L^j_{B(U)/A(U)}`: the degree-`j` terms of the cotangent
complexes of the ring maps on sections, with the maps of the restriction squares as restriction
maps. Its underlying presheaf of abelian groups is the degree-`j` part of the presheaf
`CategoryTheory.Sheaf.sectionwiseCotangentComplex`. -/
noncomputable def sectionwiseCotangentTerm (j : ℤ) :
    PresheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj where
  obj U := (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
    (sectionsAlgebra J f U)).X j
  map g := (CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
    (sectionsRestrictionSquare J f g)).f j
  map_id U := by
    by_cases hj : 0 < j
    · exact (CommAlgCat.cotangentComplex_isZero_pos.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U) j hj).eq_of_src _ _
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
      refine sectionsCotangentComplex_hom_ext J f U n _ _ fun p => ?_
      change (CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f (𝟙 U))).f (-(n : ℤ))
        (sectionsCotangentDifferential' J f U n p) = sectionsCotangentDifferential' J f U n p
      rw [squareCotangentComplexMap_sectionsCotangentDifferential',
        sectionsRestrictionSquare_id, CommAlgCat.squareFunctoriality_resolution_id]
      rfl
  map_comp {U V W} g h := by
    by_cases hj : 0 < j
    · exact (CommAlgCat.cotangentComplex_isZero_pos.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U) j hj).eq_of_src _ _
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
      refine sectionsCotangentComplex_hom_ext J f U n _ _ fun p => ?_
      change (CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f (g ≫ h))).f (-(n : ℤ))
          (sectionsCotangentDifferential' J f U n p) =
        (CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
          (sectionsRestrictionSquare J f h)).f (-(n : ℤ))
          ((CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
            (sectionsRestrictionSquare J f g)).f (-(n : ℤ))
            (sectionsCotangentDifferential' J f U n p))
      rw [squareCotangentComplexMap_sectionsCotangentDifferential',
        squareCotangentComplexMap_sectionsCotangentDifferential',
        squareCotangentComplexMap_sectionsCotangentDifferential', sectionsRestrictionSquare_comp,
        CommAlgCat.squareFunctoriality_resolution_comp]
      rfl

/-- The canonical map from the presheaf `U ↦ L^j_{B(U)/A(U)}` to the degree-`j` term of `L_{B/A}`:
over `U` it is the canonical map `L_{B(U)/A(U)} ⟶ L_{B/A}(U)` in degree `j`. -/
noncomputable def sectionwiseCotangentTermComparison (j : ℤ) :
    sectionwiseCotangentTerm J f j ⟶ ((cotangentComplex J f).X j).val where
  app U := (sectionsCotangentComplexComparison J f U).f j
  naturality g := (sectionsCotangentComplexComparison_restriction_degree J f g j).symm

attribute [local instance] moduleOfSections

/-- A derivation of a presheaf of rings `Q`, with values in a sheaf of `B`-modules whose scalars
are restricted along a map `ε : R ⟶ B` of sheaves of rings and then along `c : Q ⟶ R`, given by
its additive components. -/
def sectionwiseDerivation {A R B : Sheaf J CommRingCat.{max u v w}} (ε : R ⟶ B)
    (Q : Cᵒᵖ ⥤ CommRingCat.{max u v w}) (b : A.obj ⟶ Q) (c : Q ⟶ R.obj)
    (M : targetModules J B) (d : ∀ U, Q.obj U →+ M.val.obj U)
    (hbase : ∀ U x, d U (b.app U x) = 0)
    (hmul : ∀ U p q, d U (p * q) =
      ε.hom.app U (c.app U p) • d U q + ε.hom.app U (c.app U q) • d U p)
    (hnat : ∀ {U V} (g : U ⟶ V) p, d V (Q.map g p) = M.val.map g (d U p)) :
    PresheafOfModulesOfCommRing.Derivation' ((PresheafOfModules.restrictScalars
      (Functor.whiskerRight c (forget₂ CommRingCat RingCat))).obj
      ((SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map ε)).obj M).val) b where
  d {U} := d U
  d_app {U} := hbase U
  d_mul {U} := hmul U
  d_map g := hnat g

/-- The pure differential `1 ⊗ d -` of `L_{B(U)/A(U)}` in degree `-n`, as an additive map. -/
noncomputable def sectionsCotangentDifferentialAddHom (U : Cᵒᵖ) (n : ℕ) :
    (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).left.obj (op ⦋n⦌) →+
      (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).X (-(n : ℤ)) :=
  (CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U) n).inv.hom.toAddMonoidHom.comp
    { toFun := CommAlgCat.cotangentTermDifferential.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U) (op ⦋n⦌)
      map_zero' := by
        rw [← map_zero (algebraMap (A.obj.obj U) ((CommAlgCat.standardResolution.{max u v w,
          max u v w} (A.obj.obj U) (sectionsAlgebra J f U)).left.obj (op ⦋n⦌))),
          CommAlgCat.cotangentTermDifferential_algebraMap]
      map_add' := CommAlgCat.cotangentTermDifferential_add.{max u v w, max u v w} _ _ _ }

/-- The additive map `1 ⊗ d -` is the pure differential. -/
theorem sectionsCotangentDifferentialAddHom_apply (U : Cᵒᵖ) (n : ℕ) (p) :
    sectionsCotangentDifferentialAddHom J f U n p = sectionsCotangentDifferential' J f U n p :=
  rfl

/-- The pure differential `1 ⊗ d -` kills the image of `A(U)`. -/
theorem sectionsCotangentDifferential_algebraMap (U : Cᵒᵖ) (n : ℕ) (a : A.obj.obj U) :
    sectionsCotangentDifferential' J f U n (algebraMap (A.obj.obj U) _ a) = 0 := by
  unfold sectionsCotangentDifferential'
  rw [CommAlgCat.cotangentTermDifferential_algebraMap, map_zero]

/-- The Leibniz rule for the pure differential `1 ⊗ d -`. -/
theorem sectionsCotangentDifferential_mul (U : Cᵒᵖ) (n : ℕ)
    (p q : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj (op ⦋n⦌)) :
    sectionsCotangentDifferential' J f U n (p * q) =
      CommAlgCat.standardResolutionAugmentationHom.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U) (op ⦋n⦌) p • sectionsCotangentDifferential' J f U n q +
        CommAlgCat.standardResolutionAugmentationHom.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U) (op ⦋n⦌) q • sectionsCotangentDifferential' J f U n p := by
  unfold sectionsCotangentDifferential'
  rw [CommAlgCat.cotangentTermDifferential_mul, map_add, map_smul, map_smul]

/-- The additive components of the derivation attached to a map of presheaves of modules out of
`U ↦ L^{-n}_{B(U)/A(U)}`. -/
noncomputable def sectionwiseCotangentTermDerivationAddHom (n : ℕ) (M : targetModules J B)
    (φ : sectionwiseCotangentTerm J f (-(n : ℤ)) ⟶ M.val) (U : Cᵒᵖ) :
    (sectionwiseResolutionPresheaf J f (op ⦋n⦌)).obj U →+ M.val.obj U :=
  AddMonoidHom.comp (M := (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj (op ⦋n⦌))
    (N := (CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).X (-(n : ℤ)))
    (φ.app U).hom.toAddMonoidHom (sectionsCotangentDifferentialAddHom J f U n)

/-- The additive components are `p ↦ φ(1 ⊗ d p)`. -/
theorem sectionwiseCotangentTermDerivationAddHom_apply (n : ℕ) (M : targetModules J B)
    (φ : sectionwiseCotangentTerm J f (-(n : ℤ)) ⟶ M.val) (U : Cᵒᵖ) (p) :
    sectionwiseCotangentTermDerivationAddHom J f n M φ U p =
      φ.app U (sectionsCotangentDifferential' J f U n p) :=
  rfl

/-- The additive components kill the image of `A`. -/
theorem sectionwiseCotangentTermDerivationAddHom_base (n : ℕ) (M : targetModules J B)
    (φ : sectionwiseCotangentTerm J f (-(n : ℤ)) ⟶ M.val) (U : Cᵒᵖ) (a : A.obj.obj U) :
    sectionwiseCotangentTermDerivationAddHom J f n M φ U
      ((sectionwiseResolutionBase J f (op ⦋n⦌)).app U a) = 0 := by
  rw [sectionwiseCotangentTermDerivationAddHom_apply]
  exact (congrArg (φ.app U) (sectionsCotangentDifferential_algebraMap J f U n a)).trans
    (map_zero _)

/-- The additive components satisfy the Leibniz rule over the augmentation. -/
theorem sectionwiseCotangentTermDerivationAddHom_mul (n : ℕ) (M : targetModules J B)
    (φ : sectionwiseCotangentTerm J f (-(n : ℤ)) ⟶ M.val) (U : Cᵒᵖ)
    (p q : (sectionwiseResolutionPresheaf J f (op ⦋n⦌)).obj U) :
    sectionwiseCotangentTermDerivationAddHom J f n M φ U (p * q) =
      (resolutionAugmentation J f (op ⦋n⦌)).hom.app U
          ((sectionwiseResolutionComparison J f (op ⦋n⦌)).app U p) •
        sectionwiseCotangentTermDerivationAddHom J f n M φ U q +
      (resolutionAugmentation J f (op ⦋n⦌)).hom.app U
          ((sectionwiseResolutionComparison J f (op ⦋n⦌)).app U q) •
        sectionwiseCotangentTermDerivationAddHom J f n M φ U p := by
  rw [sectionwiseCotangentTermDerivationAddHom_apply,
    sectionwiseCotangentTermDerivationAddHom_apply,
    sectionwiseCotangentTermDerivationAddHom_apply]
  refine (congrArg (φ.app U) (sectionsCotangentDifferential_mul J f U n p q)).trans ?_
  refine ((φ.app U).hom.map_add _ _).trans ?_
  refine congrArg₂ (· + ·) (((φ.app U).hom.map_smul _ _).trans ?_)
    (((φ.app U).hom.map_smul _ _).trans ?_)
  · exact congrArg (· • φ.app U (sectionsCotangentDifferential' J f U n q))
      (resolutionAugmentation_resolutionSectionsComparison J f U (op ⦋n⦌) p).symm
  · exact congrArg (· • φ.app U (sectionsCotangentDifferential' J f U n p))
      (resolutionAugmentation_resolutionSectionsComparison J f U (op ⦋n⦌) q).symm

/-- The additive components are compatible with the restriction maps. -/
theorem sectionwiseCotangentTermDerivationAddHom_map (n : ℕ) (M : targetModules J B)
    (φ : sectionwiseCotangentTerm J f (-(n : ℤ)) ⟶ M.val) {U V : Cᵒᵖ} (g : U ⟶ V)
    (p : (sectionwiseResolutionPresheaf J f (op ⦋n⦌)).obj U) :
    sectionwiseCotangentTermDerivationAddHom J f n M φ V
        ((sectionwiseResolutionPresheaf J f (op ⦋n⦌)).map g p) =
      M.val.map g (sectionwiseCotangentTermDerivationAddHom J f n M φ U p) := by
  rw [sectionwiseCotangentTermDerivationAddHom_apply,
    sectionwiseCotangentTermDerivationAddHom_apply]
  exact (congrArg (φ.app V)
    (squareCotangentComplexMap_sectionsCotangentDifferential' J f g n p).symm).trans
      (PresheafOfModules.naturality_apply φ g _)

/-- The `A(U)`-derivations of `P'_n(U)` into a sheaf of `B`-modules `M` attached to a map of
presheaves of modules out of `U ↦ L^{-n}_{B(U)/A(U)}`: precompose with `p ↦ 1 ⊗ d p`. -/
noncomputable def sectionwiseCotangentTermDerivation (n : ℕ) (M : targetModules J B)
    (φ : sectionwiseCotangentTerm J f (-(n : ℤ)) ⟶ M.val) :
    PresheafOfModulesOfCommRing.Derivation' ((PresheafOfModules.restrictScalars
      (Functor.whiskerRight (sectionwiseResolutionComparison J f (op ⦋n⦌))
        (forget₂ CommRingCat RingCat))).obj
      ((SheafOfModules.restrictScalars (resolutionAugmentationRing J f (op ⦋n⦌))).obj
        M).val) (sectionwiseResolutionBase J f (op ⦋n⦌)) :=
  sectionwiseDerivation J (resolutionAugmentation J f (op ⦋n⦌))
    (sectionwiseResolutionPresheaf J f (op ⦋n⦌)) (sectionwiseResolutionBase J f (op ⦋n⦌))
    (sectionwiseResolutionComparison J f (op ⦋n⦌)) M
    (sectionwiseCotangentTermDerivationAddHom J f n M φ)
    (sectionwiseCotangentTermDerivationAddHom_base J f n M φ)
    (sectionwiseCotangentTermDerivationAddHom_mul J f n M φ)
    (sectionwiseCotangentTermDerivationAddHom_map J f n M φ)

/-- Under the canonical map, the pure differential `1 ⊗ d p` of `L_{B(U)/A(U)}` goes to the
universal differential of the image of `p` in `P_n(U)`. -/
theorem sectionwiseCotangentTermComparison_app_differential (n : ℕ) (U : Cᵒᵖ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj (op ⦋n⦌)) :
    (sectionwiseCotangentTermComparison J f (-(n : ℤ))).app U
        (sectionsCotangentDifferential' J f U n p) =
      (cotangentComplex_degreeIso J f n).inv.val.app U
        ((universalSheafDerivation J f (op ⦋n⦌)).d
          (((resolutionSectionsComparison J f U).app (op ⦋n⦌)).hom p)) :=
  (sectionsCotangentComplexComparison_sectionsCotangentDifferential' J f U n p).trans
    (congrArg ((cotangentComplex_degreeIso J f n).inv.val.app U)
      (cotangentTermComparison_differential J f U (op ⦋n⦌) p))

/-- Every map of presheaves of modules out of `U ↦ L^{-n}_{B(U)/A(U)}` into a sheaf of
`B`-modules factors through the canonical map to the degree-`-n` term of `L_{B/A}`. -/
theorem exists_comp_sectionwiseCotangentTermComparison (n : ℕ) (M : targetModules J B)
    (φ : sectionwiseCotangentTerm J f (-(n : ℤ)) ⟶ M.val) :
    ∃ ψ : (cotangentComplex J f).X (-(n : ℤ)) ⟶ M,
      sectionwiseCotangentTermComparison J f (-(n : ℤ)) ≫ ψ.val = φ := by
  obtain ⟨D, hD⟩ := exists_derivation_extension J (resolutionBase J f (op ⦋n⦌))
    (sectionwiseResolutionPresheaf J f (op ⦋n⦌)) (sectionwiseResolutionBase J f (op ⦋n⦌))
    (sectionwiseResolutionComparison J f (op ⦋n⦌))
    (sectionwiseResolutionBase_comp_comparison J f (op ⦋n⦌))
    (W_sectionwiseResolutionComparison J f (op ⦋n⦌))
    ((SheafOfModules.restrictScalars (resolutionAugmentationRing J f (op ⦋n⦌))).obj M)
    (sectionwiseCotangentTermDerivation J f n M φ)
  refine ⟨(cotangentComplex_degreeIso J f n).hom ≫
    ((cotangentSimplicialModule J f).derivationEquiv (op ⦋n⦌) M).symm D, ?_⟩
  apply PresheafOfModules.Hom.ext
  funext U
  refine sectionsCotangentComplex_hom_ext J f U n _ _ fun p => ?_
  show (((cotangentComplex_degreeIso J f n).hom ≫
      ((cotangentSimplicialModule J f).derivationEquiv (op ⦋n⦌) M).symm D).val.app U)
        ((sectionwiseCotangentTermComparison J f (-(n : ℤ))).app U
          (sectionsCotangentDifferential' J f U n p)) = _
  rw [sectionwiseCotangentTermComparison_app_differential]
  have key : (cotangentComplex_degreeIso J f n).inv ≫ ((cotangentComplex_degreeIso J f n).hom ≫
      ((cotangentSimplicialModule J f).derivationEquiv (op ⦋n⦌) M).symm D) =
        ((cotangentSimplicialModule J f).derivationEquiv (op ⦋n⦌) M).symm D :=
    Iso.inv_hom_id_assoc _ _
  have hd := congrArg (fun h => (((cotangentSimplicialModule J f).derivationEquiv (op ⦋n⦌) M)
    h).d (((resolutionSectionsComparison J f U).app (op ⦋n⦌)).hom p)) key
  simp only [Equiv.apply_symm_apply,
    CotangentSimplicialModuleData.derivationEquiv_eq_postcomp] at hd
  exact hd.trans (hD U p)

/-- Two maps out of the degree-`-n` term of `L_{B/A}` into a sheaf of `B`-modules agree as soon
as their composites with the canonical map from `U ↦ L^{-n}_{B(U)/A(U)}` agree. -/
theorem sectionwiseCotangentTermComparison_cancel (n : ℕ) (M : targetModules J B)
    (φ ψ : (cotangentComplex J f).X (-(n : ℤ)) ⟶ M)
    (h : sectionwiseCotangentTermComparison J f (-(n : ℤ)) ≫ φ.val =
      sectionwiseCotangentTermComparison J f (-(n : ℤ)) ≫ ψ.val) : φ = ψ := by
  refine (cancel_epi (cotangentComplex_degreeIso J f n).inv).mp ?_
  refine ((cotangentSimplicialModule J f).derivationEquiv (op ⦋n⦌) M).injective ?_
  refine derivation_ext_of_W J (resolutionBase J f (op ⦋n⦌))
    (sectionwiseResolutionPresheaf J f (op ⦋n⦌)) (sectionwiseResolutionComparison J f (op ⦋n⦌))
    (W_sectionwiseResolutionComparison J f (op ⦋n⦌)) _ _ _ fun U p => ?_
  rw [CotangentSimplicialModuleData.derivationEquiv_eq_postcomp,
    CotangentSimplicialModuleData.derivationEquiv_eq_postcomp]
  have he := ConcreteCategory.congr_hom (congrArg (fun k => k.app U) h)
    (sectionsCotangentDifferential' J f U n p)
  change φ.val.app U ((sectionwiseCotangentTermComparison J f (-(n : ℤ))).app U
      (sectionsCotangentDifferential' J f U n p)) =
    ψ.val.app U ((sectionwiseCotangentTermComparison J f (-(n : ℤ))).app U
      (sectionsCotangentDifferential' J f U n p)) at he
  have h' := sectionwiseCotangentTermComparison_app_differential J f n U p
  exact (congrArg (φ.val.app U) h').symm.trans (he.trans (congrArg (ψ.val.app U) h'))

/-- Precomposition with the canonical map identifies maps out of the degree-`j` term of `L_{B/A}`
into a sheaf of `B`-modules with maps of presheaves of modules out of `U ↦ L^j_{B(U)/A(U)}`. -/
theorem bijective_sectionwiseCotangentTermComparison_comp (j : ℤ) (M : targetModules J B) :
    Function.Bijective (fun ψ : (cotangentComplex J f).X j ⟶ M =>
      sectionwiseCotangentTermComparison J f j ≫ ψ.val) := by
  by_cases hj : 0 < j
  · refine ⟨fun φ ψ _ => (cotangentComplex_isZero_pos J f j hj).eq_of_src _ _, fun φ => ⟨0, ?_⟩⟩
    apply PresheafOfModules.Hom.ext
    funext U
    exact (CommAlgCat.cotangentComplex_isZero_pos.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U) j hj).eq_of_src _ _
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
    exact ⟨fun φ ψ h => sectionwiseCotangentTermComparison_cancel J f n M φ ψ h,
      exists_comp_sectionwiseCotangentTermComparison J f n M⟩

/-- In every degree `j`, the term of the cotangent complex `L_{B/A}` of a homomorphism of sheaves
of rings is the sheafification of the presheaf of `B`-modules `U ↦ L^j_{B(U)/A(U)}` of the terms of
the cotangent complexes of the ring maps on sections, along the canonical maps
`L_{B(U)/A(U)} ⟶ L_{B/A}(U)`: the adjunct of the canonical map out of the sheafification is an
isomorphism. -/
@[stacks 08SX "the third assertion, in each degree and in sheaves of B-modules: the degree-j \
  term of L_{B/A} is the sheafification of the presheaf of B-modules U ↦ L^j_{B(U)/A(U)} along \
  the canonical maps of the first assertion"]
theorem isIso_sheafify_sectionwiseCotangentTermComparison (j : ℤ) :
    IsIso ((PresheafOfModules.sheafificationHomEquiv.{max u v w}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).symm
        (sectionwiseCotangentTermComparison J f j)) := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B
  let P := sectionwiseCotangentTerm J f j
  let L := (cotangentComplex J f).X j
  let c := sectionwiseCotangentTermComparison J f j
  let adj := PresheafOfModules.sheafificationAdjunction.{max u v w} (𝟙 R.obj)
  have he : adj.homEquiv P L = PresheafOfModules.sheafificationHomEquiv.{max u v w} (𝟙 R.obj) :=
    Equiv.ext fun g => PresheafOfModules.sheafificationAdjunction_homEquiv_apply _ g
  rw [← he, isIso_iff_coyoneda_map_bijective]
  intro M
  have hE (ψ : L ⟶ M) :
      adj.homEquiv P M ((adj.homEquiv P L).symm c ≫ ψ) = c ≫ ψ.val := by
    rw [Adjunction.homEquiv_naturality_right]
    exact congrArg (· ≫ _) ((adj.homEquiv P L).apply_symm_apply c)
  constructor
  · intro φ ψ h
    exact (bijective_sectionwiseCotangentTermComparison_comp J f j M).injective
      ((hE φ).symm.trans ((congrArg (adj.homEquiv P M) h).trans (hE ψ)))
  · intro φ
    obtain ⟨ψ, hψ⟩ :=
      (bijective_sectionwiseCotangentTermComparison_comp J f j M).surjective (adj.homEquiv P M φ)
    exact ⟨ψ, (adj.homEquiv P M).injective ((hE ψ).trans hψ)⟩

/-- The underlying presheaf of abelian groups of `U ↦ L^j_{B(U)/A(U)}` is the degree-`j` part of
the presheaf `CategoryTheory.Sheaf.sectionwiseCotangentComplex` of sectionwise cotangent
complexes. -/
theorem sectionwiseCotangentTerm_presheaf (j : ℤ) :
    (sectionwiseCotangentTerm J f j).presheaf =
      sectionwiseCotangentComplex J f ⋙ HomologicalComplex.eval _ _ j :=
  rfl

/-- The transpose along a sheafification adjunction of an isomorphism out of a sheafified presheaf
is inverted by sheafification. -/
theorem W_homEquiv_of_isIso {D : Type*} [Category D] {G : (Cᵒᵖ ⥤ D) ⥤ Sheaf J D}
    (adj : G ⊣ sheafToPresheaf J D) {P : Cᵒᵖ ⥤ D} {F : Sheaf J D} (X : G.obj P ⟶ F)
    [hX : IsIso X] :
    J.W (adj.homEquiv P F X) := by
  rw [adj.homEquiv_unit]
  exact MorphismProperty.comp_mem _ _ _ (J.W_adj_unit_app adj P)
    (ObjectProperty.isLocal_of_isIso _ _)

/-- In every degree `j`, the canonical map from the presheaf of abelian groups
`U ↦ L^j_{B(U)/A(U)}` (the degree-`j` part of `CategoryTheory.Sheaf.sectionwiseCotangentComplex`)
to the underlying presheaf of the degree-`j` term of `L_{B/A}` is inverted by sheafification. -/
theorem W_toPresheaf_sectionwiseCotangentTermComparison (j : ℤ) :
    J.W ((PresheafOfModules.toPresheaf _).map (sectionwiseCotangentTermComparison J f j)) := by
  have hiso := isIso_sheafify_sectionwiseCotangentTermComparison J f j
  have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv.{max u v w}
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)
    ((PresheafOfModules.sheafificationHomEquiv.{max u v w}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).symm
        (sectionwiseCotangentTermComparison J f j))
  have h' := (congrArg (PresheafOfModules.toPresheaf _).map
    ((PresheafOfModules.sheafificationHomEquiv.{max u v w}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).apply_symm_apply
        (sectionwiseCotangentTermComparison J f j))).symm.trans h
  have hX : IsIso ((SheafOfModules.toSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B)).map
      ((PresheafOfModules.sheafificationHomEquiv.{max u v w}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj)).symm
          (sectionwiseCotangentTermComparison J f j))) :=
    Functor.map_isIso _ _
  exact h' ▸ W_homEquiv_of_isIso J _ _ (hX := hX)

end Terms

/-- A map of presheaves of abelian groups is inverted by sheafification exactly when its
sheafification is an isomorphism. -/
theorem isIso_presheafToSheaf_map_of_W {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}} (g : P ⟶ Q)
    (hg : J.W g) : IsIso ((presheafToSheaf J AddCommGrpCat.{max u v w}).map g) :=
  (J.W_iff_isIso_map_of_adjunction (sheafificationAdjunction J _) g).mp hg

/-- A map of complexes of presheaves of abelian groups which is inverted by sheafification in
every degree has an invertible sheafification. -/
private theorem isIso_sheafify_of_W_components
    {K K' : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ℤ}
    (a : K ⟶ K') (ha : ∀ n, J.W (a.f n)) :
    IsIso (((presheafToSheaf J AddCommGrpCat.{max u v w}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map a) := by
  suffices ∀ n, IsIso ((((presheafToSheaf J AddCommGrpCat.{max u v w}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map a).f n) from HomologicalComplex.Hom.isIso_of_components _
  exact fun n => isIso_presheafToSheaf_map_of_W J _ (ha n)

/-! ## The complex `L_{B/A}` is the sheafification of `U ↦ L_{B(U)/A(U)}` -/

section Complex

variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-- The presheaf `U ↦ L_{B(U)/A(U)}` of sectionwise cotangent complexes, read as a complex of
presheaves of abelian groups. -/
noncomputable def sectionwiseCotangentPresheafComplex :
    CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ℤ where
  X j := sectionwiseCotangentComplex J f ⋙ HomologicalComplex.eval _ _ j
  d i j :=
    { app U := ((sectionwiseCotangentComplex J f).obj U).d i j
      naturality _ _ g := ((sectionwiseCotangentComplex J f).map g).comm i j }
  shape i j h := by
    ext U : 2
    exact ((sectionwiseCotangentComplex J f).obj U).shape i j h
  d_comp_d' i j k _ _ := by
    ext U : 2
    exact ((sectionwiseCotangentComplex J f).obj U).d_comp_d i j k

/-- The cotangent complex `L_{B/A}`, read as a complex of sheaves of abelian groups. -/
noncomputable abbrev cotangentComplexAb :
    CochainComplex (Sheaf J AddCommGrpCat.{max u v w}) ℤ :=
  ((SheafOfModules.toSheaf
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (cotangentComplex J f)

/-- The canonical maps `L_{B(U)/A(U)} ⟶ L_{B/A}(U)`, as a map of complexes of presheaves of abelian
groups from `U ↦ L_{B(U)/A(U)}` to the underlying presheaves of `L_{B/A}`. -/
noncomputable def sectionwiseCotangentPresheafComplexComparison :
    sectionwiseCotangentPresheafComplex J f ⟶
      ((sheafToPresheaf J AddCommGrpCat.{max u v w}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (cotangentComplexAb J f) where
  f j := (PresheafOfModules.toPresheaf _).map (sectionwiseCotangentTermComparison J f j)
  comm' i j _ := by
    ext U x
    exact (ConcreteCategory.congr_hom ((sectionsCotangentComplexComparison J f U).comm i j) x)

/-- In every degree the canonical map from `U ↦ L_{B(U)/A(U)}` to `L_{B/A}` is inverted by
sheafification. -/
theorem W_sectionwiseCotangentPresheafComplexComparison_f (j : ℤ) :
    J.W ((sectionwiseCotangentPresheafComplexComparison J f).f j) :=
  W_toPresheaf_sectionwiseCotangentTermComparison J f j

/-- The sheafification of the presheaf of complexes `U ↦ L_{B(U)/A(U)}` maps isomorphically, along
the canonical maps `L_{B(U)/A(U)} ⟶ L_{B/A}(U)`, onto the sheafification of the underlying
presheaves of `L_{B/A}`, which is `L_{B/A}` itself. -/
theorem isIso_sheafify_sectionwiseCotangentPresheafComplexComparison :
    IsIso (((presheafToSheaf J AddCommGrpCat.{max u v w}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (sectionwiseCotangentPresheafComplexComparison J f)) :=
  isIso_sheafify_of_W_components J _ (W_sectionwiseCotangentPresheafComplexComparison_f J f)

/-- The cotangent complex `L_{B/A}` of a homomorphism of sheaves of rings is the sheafification of
the rule `U ↦ L_{B(U)/A(U)}`: the sheafification of the presheaf of complexes of abelian groups
`U ↦ L_{B(U)/A(U)}` is isomorphic to `L_{B/A}`, by the canonical maps followed by the counit of
sheafification. -/
@[stacks 08SX "the third assertion: L_{B/A} is the sheafification of U ↦ L_{B(U)/A(U)}, the \
  sheafification of the presheaf of complexes of abelian groups U ↦ L_{B(U)/A(U)} being isomorphic \
  to L_{B/A} along the canonical maps of the first assertion; degreewise, in sheaves of \
  B-modules, this is isIso_sheafify_sectionwiseCotangentTermComparison"]
noncomputable def sheafifiedSectionwiseCotangentComplexIso :
    ((presheafToSheaf J AddCommGrpCat.{max u v w}).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sectionwiseCotangentPresheafComplex J f) ≅ cotangentComplexAb J f :=
  have := isIso_sheafify_sectionwiseCotangentPresheafComplexComparison J f
  asIso (((presheafToSheaf J AddCommGrpCat.{max u v w}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (sectionwiseCotangentPresheafComplexComparison J f)) ≪≫
    (NatIso.mapHomologicalComplex
      (asIso (sheafificationAdjunction J AddCommGrpCat.{max u v w}).counit) (ComplexShape.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app (cotangentComplexAb J f)

end Complex

/-! ## Quasi-isomorphisms detected on sections -/

section QuasiIso

/-- **Quasi-isomorphisms of complexes of sheaves are detected sectionwise.** Let `φ : K ⟶ K'` be a
map of complexes of sheaves of abelian groups, and let `K₀ ⟶ K`, `K₀' ⟶ K'` be maps from complexes
of presheaves of abelian groups which are, in every degree, inverted by sheafification. If a map
`φ₀ : K₀ ⟶ K₀'` compatible with `φ` is a quasi-isomorphism of complexes of presheaves — that is,
sectionwise — then `φ` is a quasi-isomorphism. -/
theorem quasiIso_of_sectionwise
    {K K' : CochainComplex (Sheaf J AddCommGrpCat.{max u v w}) ℤ}
    {K₀ K₀' : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) ℤ}
    (a : K₀ ⟶ ((sheafToPresheaf J _).mapHomologicalComplex _).obj K)
    (a' : K₀' ⟶ ((sheafToPresheaf J _).mapHomologicalComplex _).obj K')
    (ha : ∀ n, J.W (a.f n)) (ha' : ∀ n, J.W (a'.f n))
    (φ : K ⟶ K') (φ₀ : K₀ ⟶ K₀')
    (hcomm : φ₀ ≫ a' = a ≫ ((sheafToPresheaf J _).mapHomologicalComplex _).map φ)
    [QuasiIso φ₀] : QuasiIso φ := by
  let F := presheafToSheaf J AddCommGrpCat.{max u v w}
  let ι := sheafToPresheaf J AddCommGrpCat.{max u v w}
  have := isIso_sheafify_of_W_components J a ha
  have := isIso_sheafify_of_W_components J a' ha'
  have h₁ : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ₀ ≫
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).map a') := inferInstance
  rw [← Functor.map_comp, hcomm, Functor.map_comp] at h₁
  have h₂ : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((ι.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) :=
    (quasiIso_iff_comp_left _ _).mp h₁
  let e : ι ⋙ F ≅ 𝟭 _ := asIso (sheafificationAdjunction J AddCommGrpCat.{max u v w}).counit
  let E := NatIso.mapHomologicalComplex e (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)
  exact (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk (E.app K) (E.app K')
    (E.hom.naturality φ).symm)).mp h₂

end QuasiIso

end CategoryTheory.Sheaf

end
