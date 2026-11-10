module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.ChainMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexFunctoriality
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.BaseChangeHomQI

/-!
# Naturality of the chain-level comparison map of Stacks 0E50

The comparison map `ψ : (ε^* Hom^•_A(P, I)~)^lift ⟶ SheafHom^•(ε^* P̃, J)` attached to
`ι : ε^* Ĩ ⟶ J` is natural in the source complex `P` and in the triple `(I, J, ι)`.

## Main results

* `AlgebraicGeometry.AffineEtaleDuality.compMap_naturality`: the comparison map is natural in
  `P` and in `(I, J, ι)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.AffineEtaleDuality

variable {A : CommRingCat.{u}} {B : BigEtaleSite.{u}} {hX : B.Contains (Spec A)}

/-- The morphism of `A`-module Hom complexes `Hom^•_A(P, I) ⟶ Hom^•_A(P', I')` induced by
`f : P' ⟶ P` and `g : I ⟶ I'`. -/
abbrev dcMap {P' P I I' : CochainComplex (ModuleCat.{u} A) ℤ} (f : P' ⟶ P) (g : I ⟶ I') :
    Dc P I ⟶ Dc P' I' :=
  (StacksDraft.DerivedHom.Model.homComplexFunctor A).map
    (X := (op P, I)) (Y := (op P', I')) (f.op, g)

/-- The components of the image of a cochain `d` under `dcMap f g` are
`f.f p ≫ d.v p q hpq ≫ g.f q`. -/
lemma dcMap_v {P' P I I' : CochainComplex (ModuleCat.{u} A) ℤ} (f : P' ⟶ P) (g : I ⟶ I')
    (n : ℤ) (d : Cochain P I n) (p q : ℤ) (hpq : p + n = q) :
    (((dcMap f g).f n).hom d : Cochain P' I' n).v p q hpq = f.f p ≫ d.v p q hpq ≫ g.f q := by
  change (((Cochain.ofHom f).comp d (zero_add n)).comp (Cochain.ofHom g) (add_zero n)).v p q hpq = _
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    Category.assoc]

/-- **Pre- and postcomposition with quasi-isomorphisms is a quasi-isomorphism of `A`-module Hom
complexes into K-injective complexes.** -/
lemma quasiIso_dcMap {P' P I I' : CochainComplex (ModuleCat.{u} A) ℤ} (f : P' ⟶ P) (g : I ⟶ I')
    [QuasiIso f] [QuasiIso g] [I.IsKInjective] [I'.IsKInjective] : QuasiIso (dcMap f g) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})]
  have : QuasiIso (homComplexMap f g) := homComplexMap_quasiIso f g
  refine (quasiIso_iff_of_arrow_mk_iso _ (homComplexMap f g)
    (Arrow.isoMk (Stacks.FlatBaseChangeHom.homComplexRForgetIso P I)
      (Stacks.FlatBaseChangeHom.homComplexRForgetIso P' I') ?_)).2 this
  ext n : 1
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun z => ?_)
  change Cochain P I n at z
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  exact (homComplexMap_f_apply f g n z ▸ cochainMap_v f g n p q hpq z).trans
    (dcMap_v f g n z p q hpq).symm

/-- **The comparison map is natural** in the source complex and in the target triple. -/
theorem compMap_naturality {P' P I I' : CochainComplex (ModuleCat.{u} A) ℤ}
    {J J' : CochainComplex (Mod A B hX) ℤ}
    (ι : ((epsT A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    (ι' : ((epsT A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).obj I' ⟶ J')
    (f : P' ⟶ P) (g : I ⟶ I') (h : J ⟶ J')
    (w : ((epsT A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).map g ≫ ι' = ι ≫ h) :
    ((Up A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((epsT A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).map (dcMap f g)) ≫
        compMap (P := P') ι' =
      compMap (P := P) ι ≫ RingedSite.homMap (Xs A B hX)
        (((epsT A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).map f) h := by
  ext n : 1
  refine up_hom_ext (M := (Dc P I).X n) _ _ (fun d => ?_)
  change (phiN ι' n).val.app (op (top A B hX)) (ULift.up
      (((epsT A B hX).map ((dcMap f g).f n)).val.app (op (top A B hX))
        (unitSection A B hX ((Dc P I).X n) d))) =
    ((RingedSite.homMap (Xs A B hX)
      (((epsT A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).map f) h).f n).val.app
        (op (top A B hX)) ((phiN ι n).val.app (op (top A B hX))
          (ULift.up (unitSection A B hX ((Dc P I).X n) d)))
  rw [unitSection_naturality]
  refine (phiN_app_top ι' n _).trans ?_
  refine Eq.trans ?_ (congrArg (((RingedSite.homMap (Xs A B hX)
      (((epsT A B hX).mapHomologicalComplex (ComplexShape.up ℤ)).map f) h).f n).val.app
        (op (top A B hX))) (phiN_app_top ι n d)).symm
  apply (ConcreteCategory.bijective_of_isIso (((RingedSite.sheafHomComplex (Xs A B hX)
    (Fc P') J').sectionsIso (top A B hX)).hom.f n)).1
  refine (sectionsIso_hom_topSection ι' (((dcMap f g).f n).hom d)).trans ?_
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  refine Eq.trans ?_ (RingedSite.sectionsIso_homMap_v (Xs A B hX) _ h (top A B hX) n p q hpq
    (topSection ι d)).symm
  refine (topCochain_v ι' _ p q hpq).trans ?_
  have e1 := congrArg (fun z => z.v p q hpq) (sectionsIso_hom_topSection ι (n := n) d)
  refine Eq.trans ?_ (congrArg (fun z => _ ≫ z ≫ _) e1).symm
  refine Eq.trans ?_ (congrArg (fun z => _ ≫ z ≫ _) (topCochain_v ι d p q hpq)).symm
  have e2 := dcMap_v f g n d p q hpq
  have wq : (epsT A B hX).map (g.f q) ≫ ι'.f q = ι.f q ≫ h.f q :=
    congrArg (fun φ => HomologicalComplex.Hom.f φ q) w
  have aux : ∀ x : P.X p ⟶ I.X q,
      (SheafOfModules.overFunctor (O A B hX) (top A B hX)).map
        ((epsT A B hX).map (f.f p ≫ x ≫ g.f q) ≫ ι'.f q) =
      (SheafOfModules.overFunctor (O A B hX) (top A B hX)).map ((epsT A B hX).map (f.f p)) ≫
        (SheafOfModules.overFunctor (O A B hX) (top A B hX)).map ((epsT A B hX).map x ≫ ι.f q) ≫
          (SheafOfModules.overFunctor (O A B hX) (top A B hX)).map (h.f q) := by
    intro x
    have hx : (epsT A B hX).map (f.f p ≫ x ≫ g.f q) ≫ ι'.f q =
        (epsT A B hX).map (f.f p) ≫ ((epsT A B hX).map x ≫ ι.f q) ≫ h.f q := by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, wq,
        Category.assoc]
    rw [hx, Functor.map_comp, Functor.map_comp]
  rw [e2]
  exact aux _

end AlgebraicGeometry.AffineEtaleDuality

end
