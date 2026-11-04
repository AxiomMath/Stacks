module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietoris
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# The two comparison maps out of the intersection of an elementary distinguished square

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and let `P = U ×_X V` be its intersection.  Write `(-)|_Y` for restriction of
modules along an étale morphism `j_Y : Y ⟶ X` and `j_{Y!}` for a left adjoint of it, extension
by zero, with counit `j_{Y!}(F|_Y) ⟶ F`.  The morphism `j_P` factors through both legs of the
square, and each factorization produces a comparison map
`j_{P!}(F|_P) ⟶ j_{U!}(F|_U)` and `j_{P!}(F|_P) ⟶ j_{V!}(F|_V)`, namely the adjoint of the unit
of the other leg read through the composition comparison for restriction.  Both comparisons
are compatible with the counits, so

`0 ⟶ j_{P!}F|_P ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ 0`

with maps `(a, -b)` and the sum of the two counits is a complex.  Its exactness, which is
Stacks 08GV part (1), is
`AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris` of
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisTag`.

## Main definitions

* `CategoryTheory.Adjunction.factorUnit` and
  `CategoryTheory.Adjunction.factorLeftAdjointComparison`: for composable functors `R`, `Q`
  with `R ⋙ Q ≅ T` and left adjoints `L ⊣ T` and `L' ⊣ R`, the canonical comparison
  `T ⋙ L ⟶ R ⋙ L'` of the two left adjoints.
* `AlgebraicGeometry.Space.etaleModulePullbackFactorIso`: the composition comparison for
  restriction of modules along a factorization of an étale morphism of algebraic spaces.
* `AlgebraicGeometry.Space.edsShriekOpenComparison` and
  `AlgebraicGeometry.Space.edsShriekEtaleComparison`: the two comparison maps out of the
  intersection of an elementary distinguished square.

## Main results

* `CategoryTheory.Adjunction.factorLeftAdjointComparison_comp_counit`: the comparison of left
  adjoints followed by the counit of `L' ⊣ R` is the counit of `L ⊣ T`.
* `AlgebraicGeometry.Space.edsShriekOpenComparison_comp_counit` and
  `AlgebraicGeometry.Space.edsShriekEtaleComparison_comp_counit`: each comparison map out of
  the intersection, followed by the counit of its leg, is the counit of the intersection.
* `AlgebraicGeometry.Space.zero_edsShriekMayerVietoris`: the Mayer–Vietoris short complex of
  extensions by zero is a complex, and
  `AlgebraicGeometry.Space.zero_edsLowerShriekMayerVietoris` is the same for the extension by
  zero of `AlgebraicGeometry.Space.etaleModuleLowerShriek`.

## Implementation notes

The comparison of left adjoints is defined, not existentially quantified: for a factorization
`f ≫ g = k` the map `k_!((-)|_k) ⟶ g_!((-)|_g)` is the adjoint, under the adjunction along `k`,
of the unit along `g` restricted along `f`, read through the composition comparison for
restriction.  Nothing beyond the two adjunctions and that comparison enters, so the
construction applies to any choice of extension by zero, in particular to
`AlgebraicGeometry.Space.etaleModuleLowerShriekAdjunction`.

The composition comparison used for restriction is
`AlgebraicGeometry.Space.modulePullbackCompIso`, the inverse-image half of Stacks 03LU,
transported along `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, which is the
identification of Stacks 03LW of the pullback of modules along an étale morphism with étale
restriction.

The two maps out of the intersection are the maps of the square and not merely maps compatible
with the counits, which do not determine them: the first comes from the factorization of `j_P`
through `U`, which holds by definition of `j_P`, and the second from the factorization through
`V`, which is the commutativity of the cartesian square.

## References

* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory

section FactorComparison

variable {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E] (R : A ⥤ D) (Q : D ⥤ E) (T : A ⥤ E) (e : R ⋙ Q ≅ T) {L : E ⥤ A}
  {L' : D ⥤ A}

/-- For composable functors `R : A ⥤ D` and `Q : D ⥤ E` with an identification
`e : R ⋙ Q ≅ T` and a left adjoint `L' ⊣ R`, the unit of `L' ⊣ R` restricted along `Q` and
read through `e`, as a natural transformation `T ⟶ (R ⋙ L') ⋙ T`. -/
def Adjunction.factorUnit (adj' : L' ⊣ R) : T ⟶ (R ⋙ L') ⋙ T :=
  e.inv ≫
    Functor.whiskerLeft R ((Functor.leftUnitor Q).inv ≫
      Functor.whiskerRight adj'.unit Q ≫
      (Functor.associator L' R Q).hom ≫ Functor.whiskerLeft L' e.hom) ≫
    (Functor.associator R L' T).inv

/-- **The comparison of the left adjoints attached to a factorization.** For composable
functors `R : A ⥤ D` and `Q : D ⥤ E` with `e : R ⋙ Q ≅ T` and left adjoints `L ⊣ T` and
`L' ⊣ R`, this is the canonical natural transformation `T ⋙ L ⟶ R ⋙ L'`: the adjoint, under
`L ⊣ T`, of `CategoryTheory.Adjunction.factorUnit`. -/
def Adjunction.factorLeftAdjointComparison (adj : L ⊣ T) (adj' : L' ⊣ R) :
    T ⋙ L ⟶ R ⋙ L' :=
  ((adj.whiskerRight A).homEquiv T (R ⋙ L')).symm (Adjunction.factorUnit R Q T e adj')

/-- **The comparison of left adjoints is compatible with the counits.** Composing it with the
counit of `L' ⊣ R` gives back the counit of `L ⊣ T`, so the two left adjoints and the
comparison form a triangle over the identity functor. -/
theorem Adjunction.factorLeftAdjointComparison_comp_counit (adj : L ⊣ T) (adj' : L' ⊣ R) :
    Adjunction.factorLeftAdjointComparison R Q T e adj adj' ≫ adj'.counit = adj.counit := by
  unfold Adjunction.factorLeftAdjointComparison
  apply ((adj.whiskerRight A).homEquiv T (𝟭 A)).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  ext M
  dsimp [Adjunction.factorUnit]
  simp only [id_comp, comp_id, assoc]
  have hnat := e.hom.naturality (adj'.counit.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hnat
  rw [← hnat, ← assoc (Q.map _), ← Q.map_comp, adj'.right_triangle_components, Q.map_id,
    id_comp, e.inv_hom_id_app]
  simp [Adjunction.homEquiv, Adjunction.whiskerRight]

end FactorComparison

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Factor

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **The composition comparison for étale restriction of modules.** For a factorization
`f ≫ g = k` of an étale morphism of algebraic spaces into two étale morphisms, restriction
along `g` followed by restriction along `f` is restriction along `k`.

This is the composition comparison `AlgebraicGeometry.Space.modulePullbackCompIso` of
Stacks 03LU for the pullback of modules, transported along the identification of Stacks 03LW
of that pullback with étale restriction. -/
def etaleModulePullbackFactorIso (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsEtale B S hS f.hom)
    (hg : IsEtale B S hS g.hom) {k : X ⟶ Z} (hk : f ≫ g = k)
    (hk' : IsEtale B S hS k.hom) :
    etaleModulePullback.{u, u} B S hS g hg ⋙ etaleModulePullback.{u, u} B S hS f hf ≅
      etaleModulePullback.{u, u} B S hS k hk' := by
  subst hk
  exact Functor.isoWhiskerRight (modulePullbackIsoEtaleModulePullback B S hS g hg).symm
        (etaleModulePullback.{u, u} B S hS f hf) ≪≫
      Functor.isoWhiskerLeft (modulePullback B S hS g)
        (modulePullbackIsoEtaleModulePullback B S hS f hf).symm ≪≫
      modulePullbackCompIso B S hS f g ≪≫
      modulePullbackIsoEtaleModulePullback B S hS (f ≫ g) hk'

end Factor

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The morphism from the intersection of an elementary distinguished square to the ambient
algebraic space is the composite through the open subspace. -/
theorem edsFst_comp_edsOpenHom :
    edsFst B S hS hsq ≫ edsOpenHom B S hS hsq = edsInterHom B S hS hsq :=
  rfl

/-- The morphism from the intersection of an elementary distinguished square to the ambient
algebraic space is also the composite through the étale algebraic space, the square being
cartesian. -/
theorem edsSnd_comp_edsEtaleHom :
    edsSnd B S hS hsq ≫ edsEtaleHom B S hS hsq = edsInterHom B S hS hsq :=
  (isPullback_edsInter B S hS hsq).w.symm

/-- Restriction to the open subspace of an elementary distinguished square followed by
restriction to the intersection is restriction to the intersection. -/
def edsFactorIsoOpen :
    etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq) ⋙
        etaleModulePullback.{u, u} B S hS (edsFst B S hS hsq) (isEtale_edsFst B S hS hsq) ≅
      etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq) :=
  etaleModulePullbackFactorIso B S hS (edsFst B S hS hsq) (edsOpenHom B S hS hsq)
    (isEtale_edsFst B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
    (edsFst_comp_edsOpenHom B S hS hsq) (isEtale_edsInterHom B S hS hsq)

/-- Restriction to the étale algebraic space of an elementary distinguished square followed by
restriction to the intersection is restriction to the intersection. -/
def edsFactorIsoEtale :
    etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq) ⋙
        etaleModulePullback.{u, u} B S hS (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq) ≅
      etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq) :=
  etaleModulePullbackFactorIso B S hS (edsSnd B S hS hsq) (edsEtaleHom B S hS hsq)
    (isEtale_edsSnd B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
    (edsSnd_comp_edsEtaleHom B S hS hsq) (isEtale_edsInterHom B S hS hsq)

variable
  {shriekU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekV : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekP : Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  (adjU : shriekU ⊣ etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq))
  (adjV : shriekV ⊣ etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq))
  (adjP : shriekP ⊣ etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq))

/-- **The comparison `j_{P!}(F|_P) ⟶ j_{U!}(F|_U)` of an elementary distinguished square**,
attached to the factorization of the morphism from the intersection through the open
subspace. -/
def edsShriekOpenComparison :
    etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq) ⋙ shriekP ⟶
      etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq) ⋙ shriekU :=
  Adjunction.factorLeftAdjointComparison _ _ _ (edsFactorIsoOpen B S hS hsq) adjP adjU

/-- **The comparison `j_{P!}(F|_P) ⟶ j_{V!}(F|_V)` of an elementary distinguished square**,
attached to the factorization of the morphism from the intersection through the étale
algebraic space. -/
def edsShriekEtaleComparison :
    etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq) ⋙ shriekP ⟶
      etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq) ⋙ shriekV :=
  Adjunction.factorLeftAdjointComparison _ _ _ (edsFactorIsoEtale B S hS hsq) adjP adjV

/-- The comparison through the open subspace, followed by the counit
`j_{U!}(F|_U) ⟶ F`, is the counit `j_{P!}(F|_P) ⟶ F` of the intersection. -/
theorem edsShriekOpenComparison_comp_counit :
    edsShriekOpenComparison B S hS hsq adjU adjP ≫ adjU.counit = adjP.counit :=
  Adjunction.factorLeftAdjointComparison_comp_counit _ _ _ _ adjP adjU

/-- The comparison through the étale algebraic space, followed by the counit
`j_{V!}(F|_V) ⟶ F`, is the counit `j_{P!}(F|_P) ⟶ F` of the intersection. -/
theorem edsShriekEtaleComparison_comp_counit :
    edsShriekEtaleComparison B S hS hsq adjV adjP ≫ adjV.counit = adjP.counit :=
  Adjunction.factorLeftAdjointComparison_comp_counit _ _ _ _ adjP adjV

section Complex

variable [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The Mayer–Vietoris sequence of extensions by zero is a complex.** For a sheaf of
`𝒪_X`-modules `F` the map `(a, -b)` built from the two comparisons out of the intersection,
followed by the sum of the two counits, vanishes: both comparisons followed by their counits
give the counit of the intersection, and the two contributions cancel. -/
theorem zero_edsShriekMayerVietoris (F : Modules.{u, u} B S hS W.1 W.2) :
    biprod.lift ((edsShriekOpenComparison B S hS hsq adjU adjP).app F)
        (-((edsShriekEtaleComparison B S hS hsq adjV adjP).app F)) ≫
      biprod.desc (adjU.counit.app F) (adjV.counit.app F) = 0 := by
  have hU := NatTrans.congr_app
    (edsShriekOpenComparison_comp_counit B S hS hsq adjU adjP) F
  have hV := NatTrans.congr_app
    (edsShriekEtaleComparison_comp_counit B S hS hsq adjV adjP) F
  dsimp only [NatTrans.comp_app] at hU hV
  simp only [biprod.lift_desc, Preadditive.neg_comp, hU, hV, add_neg_cancel]

/-- **The Mayer–Vietoris sequence of the extension by zero of
`AlgebraicGeometry.Space.etaleModuleLowerShriek` is a complex**, the case of
`AlgebraicGeometry.Space.zero_edsShriekMayerVietoris` in which the three extensions by zero
are the chosen left adjoints of restriction and the three adjunctions are
`AlgebraicGeometry.Space.etaleModuleLowerShriekAdjunction`. -/
theorem zero_edsLowerShriekMayerVietoris (F : Modules.{u, u} B S hS W.1 W.2) :
    biprod.lift
          ((edsShriekOpenComparison B S hS hsq
            (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
              (isEtale_edsOpenHom B S hS hsq))
            (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq))).app F)
          (-((edsShriekEtaleComparison B S hS hsq
            (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
              (isEtale_edsEtaleHom B S hS hsq))
            (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq))).app F)) ≫
        biprod.desc
          ((etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
            (isEtale_edsOpenHom B S hS hsq)).counit.app F)
          ((etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
            (isEtale_edsEtaleHom B S hS hsq)).counit.app F) = 0 :=
  zero_edsShriekMayerVietoris B S hS hsq _ _ _ F

end Complex

end Square

end AlgebraicGeometry.Space

end
