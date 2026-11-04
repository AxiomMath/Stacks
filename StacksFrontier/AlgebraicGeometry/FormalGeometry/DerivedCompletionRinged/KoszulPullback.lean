module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackObjUnitToUnitGlobalSectionSmul
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CechBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulSectionsProjection
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSite
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.UnitComparison

/-!
# The inverse image of a Koszul complex

Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism of ringed sites, let `t_1, …, t_r` be global
sections of `𝒪` and let `g_1, …, g_r` be global sections of `𝒪'` with `g_i = f^♯(t_i)`. This
file identifies the degreewise inverse image of the Koszul complex on the powers of the `t_i`
with the Koszul complex on the powers of the `g_i`:

`f^*K(𝒪, t_1^{n+1}, …, t_r^{n+1}) ≅ K(𝒪', g_1^{n+1}, …, g_r^{n+1})`,

compatibly with the transition maps of the two towers. This is the identification
`Lf^*K(𝒪, t_1^n, …, t_r^n) = K(𝒪', g_1^n, …, g_r^n)` that the proof of [Stacks, Tag 0A0G] uses,
at the level of complexes.

## Main results

* `AlgebraicGeometry.RingedSite.pullback_koszulValue`: `f^♯` carries the monomial
  `∏_i t_i^{e_i}` to `∏_i g_i^{e_i}`.
* `AlgebraicGeometry.RingedSite.pullbackKoszulPowerFunctorIso`: the inverse image carries the
  system of copies of `𝒪` underlying the Koszul complex to the one underlying the Koszul complex
  on the `g_i`.
* `AlgebraicGeometry.RingedSite.pullbackKoszulPowerComplexIso`:
  **`f^*K(𝒪, t^{n+1}) ≅ K(𝒪', g^{n+1})`**.
* `AlgebraicGeometry.RingedSite.pullbackKoszulPowerComplexIso_naturality`: it is compatible with
  the transition maps of the two towers.
* `AlgebraicGeometry.RingedSite.pullbackKoszulPowerSystemIso`: the same as an isomorphism of
  towers of complexes.

## Implementation notes

*The two inputs.* The terms of the Koszul complex are finite products of copies of the structure
sheaf, so the identification needs the inverse image to preserve those products and to carry
`𝒪` to `𝒪'`. The first is formal: `f^*` is a left adjoint, hence preserves finite coproducts,
hence — being additive, between preadditive categories with finite biproducts — finite products.
The second is the comparison `SheafOfModules.pullbackObjUnitToUnit`, and its invertibility is
`AlgebraicGeometry.RingedSite.isIso_pullbackObjUnitToUnit_fSharpRing` below — nothing is
assumed for it beyond `f` being a morphism of ringed sites. Mathlib inverts that comparison only
when the functor presenting `f` is final, a condition on the underlying categories that no
morphism of sites supplies;
`Stacks.Sites.UnitComparison.isIso_pullbackObjUnitToUnit_of_isMorphismOfSites` replaces finality
by the topological hypothesis of [Stacks, Tag 00X1], which a morphism of ringed sites has by
definition.

The entries of the differential are multiplications by the monomials `∏_i t_i^{e_i}`, and that
the comparison carries them to multiplication by `∏_i g_i^{e_i}` is
`Stacks.SheafOfModules.pullbackObjUnitToUnit_comp_globalSectionToEnd` fed with
`pullback_koszulValue`.

*The shape of the proof.* Once those two inputs are in place the rest is
`CategoryTheory.AlternatingCech.mapComplexIso` — an additive, finite-product-preserving functor
commutes with the alternating Čech complex — followed by
`CategoryTheory.AlternatingCech.mapIso` at the comparison of the two systems, exactly as
`AlgebraicGeometry.RingedSite.globalSectionsKoszulPowerComplexIso` of
`KoszulSectionsProjection.lean` does for `A`-linear global sections. The compatibility with the
transition maps is `CategoryTheory.AlternatingCech.mapComplexIso_trans_mapIso_map`.

## References

* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] hasFiniteBiproducts_sheafOfModules

/-- Continuity of the functor underlying the site-presented morphism of ringed topoi attached to
a morphism of ringed sites, in the shape instance search keys on. -/
instance isContinuous_u_toRingedToposSiteHom {X Y : RingedSite.{u, u, u}}
    (f : RingedSite.Hom X Y) :
    f.toRingedToposSiteHom.u.IsContinuous (ringedTopos Y).J (ringedTopos X).J :=
  f.toRingedToposSiteHom.isContinuous

section Preserves

variable {X Y : RingedSite.{u, u, u}}
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedSite.Hom X Y)

/-- **The inverse image of sheaves of modules is additive**, being a left adjoint of the
additive direct image. This is `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_additive`,
restated at the site-presented morphism of ringed topoi attached to a morphism of ringed sites,
whose underlying site is written differently and so is not found by instance search. -/
instance additive_pullbackTopos : f.toRingedToposSiteHom.pullbackTopos.Additive := by
  have hpf : f.toRingedToposSiteHom.pushforwardTopos.Additive :=
    AlgebraicGeometry.RingedToposSiteHom.pushforwardTopos_additive f.toRingedToposSiteHom
  exact Adjunction.left_adjoint_additive
    f.toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos

/-- **The inverse image of sheaves of modules preserves finite products.** It is a left adjoint,
so it preserves finite coproducts; between preadditive categories with finite biproducts a
functor preserving zero morphisms and finite coproducts preserves finite biproducts, hence
finite products. -/
instance preservesFiniteProducts_pullbackTopos :
    PreservesFiniteProducts f.toRingedToposSiteHom.pullbackTopos where
  preserves n := by
    have hcol : PreservesColimitsOfShape (Discrete (Fin n))
        f.toRingedToposSiteHom.pullbackTopos :=
      f.toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.leftAdjoint_preservesColimits
        |>.preservesColimitsOfShape
    have hb : PreservesBiproductsOfShape (Fin n) f.toRingedToposSiteHom.pullbackTopos :=
      preservesBiproductsOfShape_of_preservesCoproductsOfShape _
    exact preservesProductsOfShape_of_preservesBiproductsOfShape _

/-- **The comparison `f^*𝒪 ⟶ 𝒪'` is invertible along a morphism of ringed sites**, with nothing
assumed beyond the morphism. A morphism of ringed sites is in particular a morphism of sites
([Stacks, Tag 00X1]), and that is enough:
`Stacks.Sites.UnitComparison.isIso_pullbackObjUnitToUnit_of_isMorphismOfSites`.

Mathlib's instance for the same conclusion asks the functor presenting the morphism to be
`Final`, a condition on the underlying categories which no morphism of sites supplies; it is
available at a morphism of ringed *spaces* and hence of schemes, but not here. -/
theorem isIso_pullbackObjUnitToUnit_fSharpRing :
    IsIso (SheafOfModules.pullbackObjUnitToUnit.{u} f.toRingedToposSiteHom.fSharpRing) :=
  Stacks.Sites.UnitComparison.isIso_pullbackObjUnitToUnit_of_isMorphismOfSites
    f.toRingedToposSiteHom.u (ringedTopos Y).J (ringedTopos X).J
    f.toRingedToposSiteHom.fSharpRing f.isMorphismOfSites

end Preserves

section Koszul

variable {X Y : RingedSite.{u, u, u}}
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  (f : RingedSite.Hom X Y) {r : ℕ}
  (t : Fin r → Presheaf.globalSections (Y.O.obj ⋙ forget CommRingCat.{u}))
  (g : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- The hypothesis relating the two generating families: `g_i` is `f^♯(t_i)`, read on sections
over every object of the target site. -/
abbrev PushGlobalSectionsCompatible : Prop :=
  ∀ (i : Fin r) (W : Y.C),
    globalSectionVal (g i) (op (f.u.obj W)) =
      (f.fsharp.hom.app (op W)).hom (globalSectionVal (t i) (op W))

variable (hg : PushGlobalSectionsCompatible f t g)

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
include hg in
/-- **`f^♯` carries the monomial `∏_i t_i^{e_i}` to `∏_i g_i^{e_i}`**, `f^♯` being a
homomorphism of rings of sections and carrying each `t_i` to `g_i`. -/
theorem pullback_koszulValue (e : Fin r → ℕ) (U : Y.Cᵒᵖ) :
    (f.fsharp.hom.app U).hom (koszulValue Y t e U) =
      koszulValue X g e (op (f.u.obj U.unop)) := by
  rw [koszulValue, koszulValue]
  refine Eq.trans (map_prod _ _ _) (Finset.prod_congr rfl fun i _ => ?_)
  rw [map_pow]
  exact congrArg (· ^ e i) (hg i U.unop).symm


omit [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
include hg in
/-- **The comparison `f^*𝒪 ⟶ 𝒪'` carries the inverse image of multiplication by the monomial
`∏_i t_i^{e_i}` to multiplication by `∏_i g_i^{e_i}`.** -/
theorem pullbackTopos_map_koszulScalar (e : Fin r → ℕ) :
    f.toRingedToposSiteHom.pullbackTopos.map (koszulScalar Y t e) ≫
        SheafOfModules.pullbackObjUnitToUnit.{u} f.toRingedToposSiteHom.fSharpRing =
      SheafOfModules.pullbackObjUnitToUnit.{u} f.toRingedToposSiteHom.fSharpRing ≫
        koszulScalar X g e :=
  Stacks.SheafOfModules.pullbackObjUnitToUnit_comp_globalSectionToEnd
    f.toRingedToposSiteHom.fSharpRing (koszulFamily X g e) (koszulFamily Y t e)
    fun U => pullback_koszulValue f t g hg e U

include hg in
/-- **The inverse image carries the system of copies of `𝒪` underlying the Koszul complex on
the `t_i` to the one underlying the Koszul complex on the `g_i`.** At each subset the comparison
is `f^*𝒪 ≅ 𝒪'`, and its naturality is `pullbackTopos_map_koszulScalar`. -/
def pullbackKoszulPowerFunctorIso (n : ℕ) :
    koszulPowerFunctor Y t n ⋙ f.toRingedToposSiteHom.pullbackTopos ≅
      koszulPowerFunctor X g n :=
  NatIso.ofComponents
    (fun _ => @asIso _ _ _ _
      (SheafOfModules.pullbackObjUnitToUnit.{u} f.toRingedToposSiteHom.fSharpRing)
      (isIso_pullbackObjUnitToUnit_fSharpRing f))
    fun {S T} _ => pullbackTopos_map_koszulScalar f t g hg (koszulExp n S T)

include hg in
/-- **The inverse image of the Koszul complex on the `(n+1)`-st powers of `t_1, …, t_r` is the
Koszul complex on the `(n+1)`-st powers of `g_1, …, g_r`.**

This is `CategoryTheory.AlternatingCech.mapComplexIso` at the inverse image — which is additive
and preserves the finite products over the subsets of `Fin r` of a given cardinality — followed
by `CategoryTheory.AlternatingCech.mapIso` at `pullbackKoszulPowerFunctorIso`. -/
def pullbackKoszulPowerComplexIso (n : ℕ) :
    (f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (koszulPowerComplex Y t n) ≅
      koszulPowerComplex X g n :=
  AlternatingCech.mapComplexIso f.toRingedToposSiteHom.pullbackTopos
      (koszulPowerFunctor Y t n) ≪≫
    AlternatingCech.mapIso (pullbackKoszulPowerFunctorIso f t g hg n)

omit [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
include hg in
/-- The comparison of the two systems is compatible with the transition maps of the two Koszul
towers: on either side the transition map at the subset `S` is multiplication by the monomial
indexed by `S`. -/
theorem pullbackKoszulPowerFunctorIso_trans (n : ℕ) :
    Functor.whiskerRight (koszulPowerTrans Y t n) f.toRingedToposSiteHom.pullbackTopos ≫
        (pullbackKoszulPowerFunctorIso f t g hg (n + 1)).hom =
      (pullbackKoszulPowerFunctorIso f t g hg n).hom ≫ koszulPowerTrans X g n := by
  refine NatTrans.ext (funext fun S => ?_)
  exact pullbackTopos_map_koszulScalar f t g hg (fun i => if i ∈ S then 1 else 0)

omit [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
include hg in
/-- **The identification is compatible with the transition maps of the two Koszul towers.** -/
theorem pullbackKoszulPowerComplexIso_naturality (n : ℕ) :
    (f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (koszulPowerComplexMap Y t n) ≫
        (pullbackKoszulPowerComplexIso f t g hg (n + 1)).hom =
      (pullbackKoszulPowerComplexIso f t g hg n).hom ≫ koszulPowerComplexMap X g n :=
  AlternatingCech.mapComplexIso_trans_mapIso_map f.toRingedToposSiteHom.pullbackTopos
    (koszulPowerTrans Y t n) (pullbackKoszulPowerFunctorIso f t g hg n)
    (pullbackKoszulPowerFunctorIso f t g hg (n + 1)) (koszulPowerTrans X g n)
    (pullbackKoszulPowerFunctorIso_trans f t g hg n)

include hg in
/-- **The inverse image carries one Koszul tower to the other**, compatibly with the transition
maps. -/
def pullbackKoszulPowerSystemMap :
    koszulPowerSystem Y t ⋙
        f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      koszulPowerSystem X g :=
  NatTrans.ofSequence
    (fun n => (pullbackKoszulPowerComplexIso f t g hg n).hom) fun n => by
    change (f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((koszulPowerSystem Y t).map (homOfLE n.le_succ)) ≫
        (pullbackKoszulPowerComplexIso f t g hg (n + 1)).hom =
      (pullbackKoszulPowerComplexIso f t g hg n).hom ≫
        (koszulPowerSystem X g).map (homOfLE n.le_succ)
    rw [show (koszulPowerSystem Y t).map (homOfLE n.le_succ) = koszulPowerComplexMap Y t n from
        Functor.ofSequence_map_homOfLE_succ _ n,
      show (koszulPowerSystem X g).map (homOfLE n.le_succ) = koszulPowerComplexMap X g n from
        Functor.ofSequence_map_homOfLE_succ _ n]
    exact pullbackKoszulPowerComplexIso_naturality f t g hg n

omit [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}] in
include hg in
/-- The morphism of towers `pullbackKoszulPowerSystemMap f t g hg` is an isomorphism. -/
theorem isIso_pullbackKoszulPowerSystemMap :
    IsIso (pullbackKoszulPowerSystemMap f t g hg) := by
  have hi (n : ℕ) : IsIso ((pullbackKoszulPowerSystemMap f t g hg).app n) := by
    show IsIso (pullbackKoszulPowerComplexIso f t g hg n).hom
    infer_instance
  exact NatIso.isIso_of_isIso_app _

include hg in
/-- **The inverse image carries one Koszul tower to the other**, as an isomorphism of towers of
complexes. -/
def pullbackKoszulPowerSystemIso :
    koszulPowerSystem Y t ⋙
        f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      koszulPowerSystem X g :=
  @asIso _ _ _ _ (pullbackKoszulPowerSystemMap f t g hg)
    (isIso_pullbackKoszulPowerSystemMap f t g hg)

end Koszul

end AlgebraicGeometry.RingedSite

end
