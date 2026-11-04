module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.Canonical
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction

/-!
# The canonical comparison of inverse images, read on sections over a chart

Along an étale morphism `g : D ⟶ C` of algebraic spaces the inverse image of modules of
Stacks 03LU is restriction of sections on the small étale site, by Stacks 03LW: a section of
`g^*M` over a chart `U` of `D` is a section of `M` over the composite chart `U ≫ g` of `C`.

Iterated étale restriction is restriction along the composite, whereas the inverse image of
modules composes only up to the comparison of Stacks 03LU. The compatibility of the two is the
predicate `AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction`.
Given it, the canonical comparison of two inverse images of Stacks 04W5 is, on sections over a
chart, the transport along the equality of the two composite charts.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleSect` reads a section of an inverse image
  along an étale morphism as a section over the composite chart.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction` is the
  compatibility of the comparison of Stacks 03LU with iterated étale restriction.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.EtaleRestrictionComp` is the same compatibility at
  a single composable pair of étale morphisms.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.smallEtalePostcomp_obj_comp` and
  `AlgebraicGeometry.Space.QuasiCoherentDescent.smallEtalePostcomp_obj_congr`: postcomposition
  of charts composes definitionally, and respects equality of morphisms.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleSect_eqToHom`: reading sections commutes
  with the transport along an equality of morphisms.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleSect_comparisonComposite`: granted the
  compatibility, the canonical comparison of two inverse images of a module along morphisms with
  equal composites, written out through the comparisons of Stacks 03LU, is, on sections over a
  chart, the transport along the equality of the two composite charts.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {A C D P Q R : AlgebraicSpaces B S hS}

/-- Postcomposition of charts composes: postcomposing along `h` and then along `g` is
postcomposing along `h ≫ g`. -/
theorem smallEtalePostcomp_obj_comp (h : D ⟶ A) (g : A ⟶ C) (hh : IsEtale B S hS h.hom)
    (hg : IsEtale B S hS g.hom) (hhg : IsEtale B S hS (h ≫ g).hom)
    (U : SmallEtale B S hS D.1) :
    (smallEtalePostcomp B S hS g hg).obj ((smallEtalePostcomp B S hS h hh).obj U) =
      (smallEtalePostcomp B S hS (h ≫ g) hhg).obj U :=
  rfl

/-- Postcomposition of charts along equal morphisms gives equal charts. -/
theorem smallEtalePostcomp_obj_congr {k l : D ⟶ C} (hk : IsEtale B S hS k.hom)
    (hl : IsEtale B S hS l.hom) (hkl : k = l) (U : SmallEtale B S hS D.1) :
    (smallEtalePostcomp B S hS k hk).obj U = (smallEtalePostcomp B S hS l hl).obj U := by
  subst hkl
  rfl

/-- A section of the inverse image `g^*M` of a module along an étale morphism `g`, over a chart
`U`, read as a section of `M` over the composite chart. -/
def etaleSect (g : D ⟶ C) (hg : IsEtale B S hS g.hom) (M : Modules.{u, u} B S hS C.1 C.2)
    (U : SmallEtale B S hS D.1)
    (m : ((modulePullback B S hS g).obj M).val.obj (.op U)) :
    M.val.obj (.op ((smallEtalePostcomp B S hS g hg).obj U)) :=
  ((modulePullbackIsoEtaleModulePullback B S hS g hg).hom.app M).val.app (.op U) m

/-- Reading sections of an inverse image along an étale morphism commutes with the transport
along an equality of morphisms: the transport of the section is the restriction of the read
section along the equality of the two composite charts. -/
theorem etaleSect_eqToHom {k l : D ⟶ C} (hk : IsEtale B S hS k.hom)
    (hl : IsEtale B S hS l.hom) (hkl : k = l) (M : Modules.{u, u} B S hS C.1 C.2)
    (U : SmallEtale B S hS D.1)
    (m : ((modulePullback B S hS k).obj M).val.obj (.op U)) :
    etaleSect B S hS l hl M U
        ((eqToHom (congrArg (fun r : D ⟶ C => (modulePullback B S hS r).obj M) hkl)).val.app
          (.op U) m) =
      eqToHom (congrArg (fun V : SmallEtale B S hS C.1 => M.val.presheaf.obj (.op V))
          (smallEtalePostcomp_obj_congr B S hS hk hl hkl U)) (etaleSect B S hS k hk M U m) := by
  subst hkl
  simp only [etaleSect, eqToHom_refl]
  rfl

/-- The compatibility of the comparison of inverse images along a composite with étale
restriction: for étale `h` and `g`, a section of the iterated inverse image, read through the
comparison of Stacks 03LU as a section of the inverse image along the composite and then as a
section over the composite chart, is that section read over the two charts in turn. -/
structure ModulePullbackCompIsoEtaleRestriction (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : Prop where
  /-- Reading a section of an iterated inverse image through the comparison of Stacks 03LU is
  reading it over the two charts in turn. -/
  comp_app : ∀ {C A D : AlgebraicSpaces B S hS} (h : D ⟶ A) (g : A ⟶ C)
      (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
      (hhg : IsEtale B S hS (h ≫ g).hom) (M : Modules.{u, u} B S hS C.1 C.2)
      (U : SmallEtale B S hS D.1)
      (m : ((modulePullback B S hS h).obj ((modulePullback B S hS g).obj M)).val.obj (.op U)),
    etaleSect B S hS (h ≫ g) hhg M U
        (((modulePullbackCompIso B S hS h g).hom.app M).val.app (.op U) m) =
      etaleSect B S hS g hg M ((smallEtalePostcomp B S hS h hh).obj U)
        (etaleSect B S hS h hh ((modulePullback B S hS g).obj M) U m)

/-- The compatibility of the comparison of Stacks 03LU with étale restriction at a single
composable pair `h`, `g` of étale morphisms: a section of the iterated inverse image along `h`
and `g`, read through the comparison as a section of the inverse image along `h ≫ g` and then as
a section over the composite chart, is that section read over the two charts in turn. -/
structure EtaleRestrictionComp (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {C' A' D' : AlgebraicSpaces B S hS} (h : D' ⟶ A') (g : A' ⟶ C')
    (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom) : Prop where
  /-- Reading a section of the iterated inverse image along this pair through the comparison of
  Stacks 03LU is reading it over the two charts in turn. -/
  comp_app : ∀ (M : Modules.{u, u} B S hS C'.1 C'.2) (U : SmallEtale B S hS D'.1)
      (m : ((modulePullback B S hS h).obj ((modulePullback B S hS g).obj M)).val.obj (.op U)),
    etaleSect B S hS (h ≫ g) hhg M U
        (((modulePullbackCompIso B S hS h g).hom.app M).val.app (.op U) m) =
      etaleSect B S hS g hg M ((smallEtalePostcomp B S hS h hh).obj U)
        (etaleSect B S hS h hh ((modulePullback B S hS g).obj M) U m)

/-- The coherence at every pair gives the coherence at a named pair. -/
theorem ModulePullbackCompIsoEtaleRestriction.toComp
    (hcomp : ModulePullbackCompIsoEtaleRestriction B S hS) {C' A' D' : AlgebraicSpaces B S hS}
    (h : D' ⟶ A') (g : A' ⟶ C') (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom) :
    EtaleRestrictionComp B S hS h g hh hg hhg :=
  ⟨hcomp.comp_app h g hh hg hhg⟩

/-- The same compatibility, read in the inverse direction of the comparison of Stacks 03LU. -/
theorem etaleSect_comp_inv (h : D ⟶ A)
    (g : A ⟶ C) (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom)
    (hcomp : EtaleRestrictionComp B S hS h g hh hg hhg)
    (M : Modules.{u, u} B S hS C.1 C.2)
    (U : SmallEtale B S hS D.1)
    (m : ((modulePullback B S hS (h ≫ g)).obj M).val.obj (.op U)) :
    etaleSect B S hS g hg M ((smallEtalePostcomp B S hS h hh).obj U)
        (etaleSect B S hS h hh ((modulePullback B S hS g).obj M) U
          (((modulePullbackCompIso B S hS h g).inv.app M).val.app (.op U) m)) =
      etaleSect B S hS (h ≫ g) hhg M U m := by
  refine (hcomp.comp_app M U
    (((modulePullbackCompIso B S hS h g).inv.app M).val.app (.op U) m)).symm.trans ?_
  refine congrArg (etaleSect B S hS (h ≫ g) hhg M U) ?_
  have h1 : ((modulePullbackCompIso B S hS h g).inv.app M).val.app (.op U) ≫
      ((modulePullbackCompIso B S hS h g).hom.app M).val.app (.op U) = 𝟙 _ := by
    rw [← PresheafOfModules.comp_app, ← SheafOfModules.comp_val, Iso.inv_hom_id_app]
    rfl
  exact CategoryTheory.congr_fun h1 m

/-- Reading a section through a composite of three isomorphisms of modules is reading it
through the three in turn. -/
theorem trans_hom_val_app {X Y Z W : Modules.{u, u} B S hS A.1 A.2} (α : X ≅ Y) (β : Y ≅ Z)
    (γ : Z ≅ W) (U : SmallEtale B S hS A.1) (m : X.val.obj (.op U)) :
    ((α ≪≫ β ≪≫ γ).hom).val.app (.op U) m =
      γ.hom.val.app (.op U) (β.hom.val.app (.op U) (α.hom.val.app (.op U) m)) :=
  rfl

/-- The canonical comparison of Stacks 04W5, written out through the comparisons of
Stacks 03LU, read on sections over a chart: granted the compatibility, it is the transport
along the equality of the two composite charts. -/
theorem etaleSect_comparisonComposite
    (a : P ⟶ Q) (b : P ⟶ R)
    (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj) (ha : IsEtale B S hS a.hom)
    (hb : IsEtale B S hS b.hom) (hfi : IsEtale B S hS fi.hom) (hfj : IsEtale B S hS fj.hom)
    (hafi : IsEtale B S hS (a ≫ fi).hom) (hbfj : IsEtale B S hS (b ≫ fj).hom)
    (hca : EtaleRestrictionComp B S hS a fi ha hfi hafi)
    (hcb : EtaleRestrictionComp B S hS b fj hb hfj hbfj)
    (M : Modules.{u, u} B S hS A.1 A.2) (U : SmallEtale B S hS P.1)
    (m : ((modulePullback B S hS a).obj ((modulePullback B S hS fi).obj M)).val.obj (.op U)) :
    etaleSect B S hS fj hfj M ((smallEtalePostcomp B S hS b hb).obj U)
        (etaleSect B S hS b hb ((modulePullback B S hS fj).obj M) U
          (((modulePullbackCompIso B S hS b fj).inv.app M).val.app (.op U)
            ((eqToHom (congrArg (fun q : P ⟶ A => (modulePullback B S hS q).obj M) h)).val.app
              (.op U) (((modulePullbackCompIso B S hS a fi).hom.app M).val.app (.op U) m)))) =
      eqToHom (congrArg (fun V : SmallEtale B S hS A.1 => M.val.presheaf.obj (.op V))
          (smallEtalePostcomp_obj_congr B S hS hafi hbfj h U))
        (etaleSect B S hS fi hfi M ((smallEtalePostcomp B S hS a ha).obj U)
          (etaleSect B S hS a ha ((modulePullback B S hS fi).obj M) U m)) := by
  rw [etaleSect_comp_inv B S hS b fj hb hfj hbfj hcb M U,
    etaleSect_eqToHom B S hS hafi hbfj h M U, hca.comp_app M U m]

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
