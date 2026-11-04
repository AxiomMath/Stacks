module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackCategory
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackProjection
public import StacksFrontier.AlgebraicGeometry.Quot.QuotToCoherentStackFunctorLaws
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory

/-!
# The morphism `Quot_{F/X/B} ⟶ Coh_{X/B}` of Stacks 0DP6: its source, its objects and its
module comparisons

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
of finite presentation and let `F` be a quasi-coherent `𝒪_X`-module — the standing data
`AlgebraicGeometry.Space.QuotSituation` of Stacks 09TR.  Stacks 0DP6 records the morphism

`Quot_{F/X/B} ⟶ Coh_{X/B}`

which sends a quotient `F_T ⟶ 𝒬` classified by `Quot_{F/X/B}(T)` to the object `𝒬` of
`Coh_{X/B}` over `T`.  Its object and morphism assignments, for the *canonical* inverse image of
a quotient, are `AlgebraicGeometry.Space.QuotSituation.cohObject` and
`AlgebraicGeometry.Space.QuotSituation.cohHom` of
`StacksFrontier/AlgebraicGeometry/Quot/QuotToCoherentStack.lean`, and their functor laws for the
module comparisons are proved in
`StacksFrontier/AlgebraicGeometry/Quot/QuotToCoherentStackFunctorLaws.lean`.

A functor out of the *category of elements* of the Quot presheaf cannot use those assignments as
they stand: a morphism of that category gives a quotient over `T'` together with an equality
identifying it with the inverse image of a quotient over `T`, not the inverse image itself.  This
file is about the assignments in that shape — over abstract test schemes and for an arbitrary
identification of the pulled-back kernel — together with the category the functor would come out
of.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.quotientFibreIso`: the identification of the quotient of
  `F_{T'}` by a kernel `K'` with the inverse image of `F_T/K`, given an identification of `K'`
  with the kernel pulled back along `h : T' ⟶ T`.  This is the module comparison a morphism of
  `Coh_{X/B}` carries, in the shape a functor's action on morphisms needs.
* `AlgebraicGeometry.Space.QuotSituation.cohHomOfData`: the morphism of `Coh_{X/B}` built from
  that comparison — the action of the morphism of Stacks 0DP6 on a morphism of test schemes
  together with such an identification.
* `AlgebraicGeometry.Space.QuotSituation.cohObjectOfFamily` and
  `AlgebraicGeometry.Space.QuotSituation.familyBaseMap`: the object of `Coh_{X/B}` and the
  morphism of test schemes over `B` attached to a quotient over a scheme of the site, that is,
  to a section of the Quot presheaf of Stacks 09TR.
* `AlgebraicGeometry.Space.QuotSituation.quotCatFiberedInGroupoids`: **`Quot_{F/X/B}` as a
  category fibred in groupoids over the big fppf site of `S`** — the category of elements of the
  Quot presheaf.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.quotientPullbackProjection_id_of_factorization`: the
  projection of `F_T` onto the inverse image of `F_T/K` along the identity is the projection onto
  `F_T/K` followed by the unit comparison of the inverse images.
* `AlgebraicGeometry.Space.QuotSituation.quotientFibreIso_hom_id_of_factorization` and
  `AlgebraicGeometry.Space.QuotSituation.quotientFibreIso_inv_id_of_factorization`: **the unit
  law for the comparison**, for an abstract unit comparison of the inverse images.
* `AlgebraicGeometry.Space.QuotSituation.quotientFibreIso_hom_comp_of_factorization` and
  `AlgebraicGeometry.Space.QuotSituation.quotientFibreIso_inv_comp_of_factorization`: **the
  composition law for the comparison**, for an abstract comparison of iterated inverse images.
* `AlgebraicGeometry.Space.QuotSituation.quotientFibreIso_inv_id` and
  `AlgebraicGeometry.Space.QuotSituation.quotientFibreIso_inv_comp`: those two laws instantiated
  at the unit and composition comparisons out of which `AlgebraicGeometry.Space.CoherentHom.id`
  and `AlgebraicGeometry.Space.CoherentHom.comp` are built, so they are the two functor laws the
  morphism of Stacks 0DP6 has to satisfy.
* `AlgebraicGeometry.Space.QuotSituation.cohHomOfData_comp`: **the composition law for the
  morphism of `Coh_{X/B}`** — the morphism attached to a composite of morphisms of test schemes,
  for any identifications of the kernels pulled back along them, is the composite in
  `Coh_{X/B}`.
* `AlgebraicGeometry.Space.QuotSituation.quotientPullback_familyBaseMap`: the kernel of a section
  of the Quot presheaf restricted along a morphism of schemes of the site is the kernel of the
  section pulled back along the induced morphism of test schemes.  This is what makes the object
  assignment above functorial on the nose.

## Implementation notes

Each law is stated twice: once with the comparison of inverse images abstracted as a variable
(`…_of_factorization`) and once instantiated at the comparison of `Coh_{X/B}`.  This is the
device the implementation notes of
`StacksFrontier/AlgebraicGeometry/Quot/QuotToCoherentStackFunctorLaws.lean` prescribe: with the
comparison abstract every statement is written in one spelling of the inverse image, and the
instantiation compares only the type of a variable with the type of the argument supplied for it,
which is an equality of isomorphisms of functors and therefore checkable.  Proving the unit law
directly at `AlgebraicGeometry.Space.CoherentSituation.idComparison` does not elaborate.

The unit law is proved by cancelling the projection `F_T ⟶ F_T/K`, an epimorphism, rather than by
comparing the two transports along the equality of kernels: every step is then an equality of
morphisms out of `F_T`.  This is the same discipline the composition law of
`StacksFrontier/AlgebraicGeometry/Quot/QuotToCoherentStackFunctorLaws.lean` follows.

`AlgebraicGeometry.Space.QuotSituation.toCoherentSituation` is made reducible at `implicit`
transparency for this module only, so that goals mentioning both a test scheme over `D.Y` and one
over `D.toCoherentSituation.Y` stay type-correct at the transparency `rw` and `simp only` use;
without it `CategoryTheory.Iso.inv_comp_eq` does not rewrite in the composition law.

`AlgebraicGeometry.Space.QuotSituation.cohHomOfData` is declared reducible at `implicit`
transparency for the same reason: the composition law compares the comparison of `Coh_{X/B}` at
the base maps of two composable morphisms with the same comparison at the two morphisms of test
schemes, and those base maps are projections of `cohHomOfData`, which have to reduce before the
comparison is reached.

`AlgebraicGeometry.Space.QuotSituation.quotCatFiberedInGroupoids` is not
`AlgebraicGeometry.Stack.fibredCategory` of the Quot presheaf: that construction is stated for
presheaves valued in the universe of the site, and a section of the Quot presheaf is a quotient,
recorded by a subobject, so it lives one universe up.  The general construction of Stacks 0049,
`CategoryTheory.presheafOfGroupoids`, is universe-polymorphic and is used directly; the resulting
category over the site has its hom-sets in the universe of those of `Coh_{X/B}`, which is where
the 1-morphism has to live.

## References

* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
* [Stacks Project, Tag 0049](https://stacks.math.columbia.edu/tag/0049)
* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08W5](https://stacks.math.columbia.edu/tag/08W5)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local implicit_reducible] QuotSituation.toCoherentSituation

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-! ### The module comparison, over abstract test schemes -/

/-- Isomorphisms with the same forward map have the same inverse. -/
private theorem iso_inv_eq_of_hom_eq {C : Type*} [Category C] {X Y : C} {e e' : X ≅ Y}
    (h : e.hom = e'.hom) : e.inv = e'.inv :=
  congrArg Iso.inv (Iso.ext h)

/-- **The module comparison a morphism of `Coh_{X/B}` carries, for an arbitrary identification
of the pulled-back kernel.**  Given `h : T' ⟶ T`, a kernel `K` of a quotient of `F_T`, a kernel
`K'` of a quotient of `F_{T'}` and an identification of `K'` with the kernel pulled back along
`h`, this identifies `F_{T'}/K'` with the inverse image of `F_T/K` along `X_{T'} ⟶ X_T`.

For `K'` the pulled-back kernel itself this is
`AlgebraicGeometry.Space.QuotientSituation.quotientPullbackCokernelIso`. -/
def quotientFibreIso {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (K' : Subobject (D.baseChangeModule T'))
    (hK : D.quotientPullback h K = K') :
    D.quotientModule T' K' ≅
      (modulePullback B S hS (D.relativeMap h)).obj (D.quotientModule T K) :=
  eqToIso (congrArg (fun J : Subobject (D.baseChangeModule T') => D.quotientModule T' J)
      hK.symm) ≪≫
    D.quotientPullbackCokernelIso h K

/-- The comparison written out: the transport along the identification of kernels followed by the
identification of the quotient by the pulled-back kernel with the inverse image. -/
theorem quotientFibreIso_hom {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (K' : Subobject (D.baseChangeModule T'))
    (hK : D.quotientPullback h K = K') :
    (D.quotientFibreIso h K K' hK).hom =
      eqToHom (congrArg (fun J : Subobject (D.baseChangeModule T') => D.quotientModule T' J)
          hK.symm) ≫
        (D.quotientPullbackCokernelIso h K).hom :=
  rfl

/-- **The projection onto the inverse image of a quotient along the identity of a test scheme**,
for an abstract unit comparison `γ` of the inverse images.  It is the projection of `F_T` onto
`F_T/K` followed by the inverse of `γ` at that quotient. -/
theorem quotientPullbackProjection_id_of_factorization {T : SchemesOver D.Y}
    (K : Subobject (D.baseChangeModule T))
    (γ : modulePullback B S hS (D.relativeMap (𝟙 T)) ≅
      𝟭 (Modules.{u, u} B S hS (D.space T).1 (D.space T).2))
    (hγ : D.baseChangeComparison (𝟙 T) =
      (Functor.rightUnitor (modulePullback B S hS (D.sourceProjection T))).symm ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS (D.sourceProjection T)) γ.symm) :
    D.quotientPullbackProjection (𝟙 T) K =
      D.quotientProjection T K ≫ γ.inv.app (D.quotientModule T K) := by
  have hdef : D.quotientPullbackProjection (𝟙 T) K =
      (D.baseChangeComparison (𝟙 T)).hom.app D.F ≫
        (modulePullback B S hS (D.relativeMap (𝟙 T))).map (D.quotientProjection T K) :=
    rfl
  rw [hdef, hγ]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_inv_app, Category.id_comp]
  have hnat := γ.inv.naturality (D.quotientProjection T K)
  simp only [Functor.id_obj, Functor.id_map] at hnat
  exact hnat.symm

/-- **The unit law for the module comparison**, for an abstract unit comparison `γ` of the
inverse images: the comparison attached to the identity of a test scheme and any identification
of the kernel pulled back along it is the inverse of `γ` at the quotient. -/
theorem quotientFibreIso_hom_id_of_factorization {T : SchemesOver D.Y}
    (K : Subobject (D.baseChangeModule T)) (hK : D.quotientPullback (𝟙 T) K = K)
    (γ : modulePullback B S hS (D.relativeMap (𝟙 T)) ≅
      𝟭 (Modules.{u, u} B S hS (D.space T).1 (D.space T).2))
    (hγ : D.baseChangeComparison (𝟙 T) =
      (Functor.rightUnitor (modulePullback B S hS (D.sourceProjection T))).symm ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS (D.sourceProjection T)) γ.symm) :
    (D.quotientFibreIso (𝟙 T) K K hK).hom = γ.inv.app (D.quotientModule T K) := by
  rw [← cancel_epi (D.quotientProjection T K), D.quotientFibreIso_hom, ← Category.assoc,
    D.quotientProjection_comp_eqToHom hK.symm,
    D.quotientProjection_comp_quotientPullbackCokernelIso_hom (𝟙 T) K,
    D.quotientPullbackProjection_id_of_factorization K γ hγ]

/-- **The unit law for the module comparison, in the direction a morphism of `Coh_{X/B}` carries
it.**  The inverse of the comparison attached to the identity of a test scheme is `γ` at the
quotient. -/
theorem quotientFibreIso_inv_id_of_factorization {T : SchemesOver D.Y}
    (K : Subobject (D.baseChangeModule T)) (hK : D.quotientPullback (𝟙 T) K = K)
    (γ : modulePullback B S hS (D.relativeMap (𝟙 T)) ≅
      𝟭 (Modules.{u, u} B S hS (D.space T).1 (D.space T).2))
    (hγ : D.baseChangeComparison (𝟙 T) =
      (Functor.rightUnitor (modulePullback B S hS (D.sourceProjection T))).symm ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS (D.sourceProjection T)) γ.symm) :
    (D.quotientFibreIso (𝟙 T) K K hK).inv = γ.hom.app (D.quotientModule T K) := by
  exact iso_inv_eq_of_hom_eq (e' := (γ.app (D.quotientModule T K)).symm)
    (D.quotientFibreIso_hom_id_of_factorization K hK γ hγ)

/-- **The composition law for the module comparison**, for an abstract comparison `τ` of
iterated inverse images: the comparison attached to a composite `h ≫ k` of morphisms of test
schemes is the comparison attached to `h`, followed by the inverse image along `X_{T''} ⟶ X_{T'}`
of the comparison attached to `k`, followed by `τ`. -/
theorem quotientFibreIso_hom_comp_of_factorization {T'' T' T : SchemesOver D.Y}
    (h : T'' ⟶ T') (k : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (K' : Subobject (D.baseChangeModule T'))
    (K'' : Subobject (D.baseChangeModule T''))
    (hK' : D.quotientPullback k K = K') (hK'' : D.quotientPullback h K' = K'')
    (hKm : D.quotientPullback (h ≫ k) K = K'')
    (τ : modulePullback B S hS (D.relativeMap (h ≫ k)) ≅
      modulePullback B S hS (D.relativeMap k) ⋙ modulePullback B S hS (D.relativeMap h))
    (hτ : D.baseChangeComparison (h ≫ k) =
      (D.baseChangeComparison h ≪≫
          Functor.isoWhiskerRight (D.baseChangeComparison k)
            (modulePullback B S hS (D.relativeMap h)) ≪≫
          Functor.associator (modulePullback B S hS (D.sourceProjection T))
            (modulePullback B S hS (D.relativeMap k))
            (modulePullback B S hS (D.relativeMap h))) ≪≫
        (Functor.isoWhiskerLeft (modulePullback B S hS (D.sourceProjection T)) τ).symm) :
    (D.quotientFibreIso (h ≫ k) K K'' hKm).hom =
      ((D.quotientFibreIso h K' K'' hK'').hom ≫
          (modulePullback B S hS (D.relativeMap h)).map
            (D.quotientFibreIso k K K' hK').hom) ≫
        τ.inv.app (D.quotientModule T K) := by
  subst hK'
  subst hK''
  rw [D.quotientFibreIso_hom, D.quotientFibreIso_hom, D.quotientFibreIso_hom]
  simp only [eqToHom_refl, Category.id_comp]
  rw [D.quotientPullbackCokernelIso_hom_comp_of_factorization h k K τ hτ hKm]
  refine (eqToHom_trans_assoc ..).trans ?_
  rw [eqToHom_refl, Category.id_comp, Category.assoc]

/-- **The composition law for the module comparison, in the direction a morphism of `Coh_{X/B}`
carries it.**  The inverse of the comparison attached to a composite is the composite that
`AlgebraicGeometry.Space.CoherentHom.comp` forms out of the two inverse comparisons, for an
abstract comparison `τ` of iterated inverse images. -/
theorem quotientFibreIso_inv_comp_of_factorization {T'' T' T : SchemesOver D.Y}
    (h : T'' ⟶ T') (k : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (K' : Subobject (D.baseChangeModule T'))
    (K'' : Subobject (D.baseChangeModule T''))
    (hK' : D.quotientPullback k K = K') (hK'' : D.quotientPullback h K' = K'')
    (hKm : D.quotientPullback (h ≫ k) K = K'')
    (τ : modulePullback B S hS (D.relativeMap (h ≫ k)) ≅
      modulePullback B S hS (D.relativeMap k) ⋙ modulePullback B S hS (D.relativeMap h))
    (hτ : D.baseChangeComparison (h ≫ k) =
      (D.baseChangeComparison h ≪≫
          Functor.isoWhiskerRight (D.baseChangeComparison k)
            (modulePullback B S hS (D.relativeMap h)) ≪≫
          Functor.associator (modulePullback B S hS (D.sourceProjection T))
            (modulePullback B S hS (D.relativeMap k))
            (modulePullback B S hS (D.relativeMap h))) ≪≫
        (Functor.isoWhiskerLeft (modulePullback B S hS (D.sourceProjection T)) τ).symm) :
    (D.quotientFibreIso (h ≫ k) K K'' hKm).inv =
      Functor.fibreComp τ (D.quotientFibreIso h K' K'' hK'').inv
        (D.quotientFibreIso k K K' hK').inv := by
  refine (iso_inv_eq_of_hom_eq (e' := (D.quotientFibreIso h K' K'' hK'' ≪≫
          (modulePullback B S hS (D.relativeMap h)).mapIso
            (D.quotientFibreIso k K K' hK')) ≪≫
        (τ.app (D.quotientModule T K)).symm)
    (D.quotientFibreIso_hom_comp_of_factorization h k K K' K'' hK' hK'' hKm τ hτ)).trans ?_
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Functor.fibreComp]
  rfl

/-! ### The two functor laws at the comparisons of `Coh_{X/B}` -/

/-- **Stacks 0DP6, the unit law for the module comparison at the unit comparison of
`Coh_{X/B}`.**  The module comparison attached to the identity of a test scheme and any
identification of the kernel pulled back along it is the unit comparison out of which
`AlgebraicGeometry.Space.CoherentHom.id` is built. -/
theorem quotientFibreIso_inv_id (hc : ModulePushforwardCoherence B S hS)
    {T : SchemesOver D.Y} (K : Subobject (D.baseChangeModule T))
    (hK : D.quotientPullback (𝟙 T) K = K) :
    (D.quotientFibreIso (𝟙 T) K K hK).inv =
      (D.toCoherentSituation.idComparison hc T).hom.app (D.quotientModule T K) :=
  D.quotientFibreIso_inv_id_of_factorization K hK (D.toCoherentSituation.idComparison hc T)
    (D.baseChangeComparison_id_idComparison hc T)

/-- **Stacks 0DP6, the composition law for the module comparison at the composition comparison
of `Coh_{X/B}`.**  The module comparison attached to a composite of morphisms of test schemes is
the composite that `AlgebraicGeometry.Space.CoherentHom.comp` forms out of the two comparisons.
-/
theorem quotientFibreIso_inv_comp (hc : ModulePushforwardCoherence B S hS)
    {T'' T' T : SchemesOver D.Y} (h : T'' ⟶ T') (k : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (K' : Subobject (D.baseChangeModule T'))
    (K'' : Subobject (D.baseChangeModule T''))
    (hK' : D.quotientPullback k K = K') (hK'' : D.quotientPullback h K' = K'')
    (hKm : D.quotientPullback (h ≫ k) K = K'') :
    (D.quotientFibreIso (h ≫ k) K K'' hKm).inv =
      Functor.fibreComp (D.toCoherentSituation.compComparison h k)
        (D.quotientFibreIso h K' K'' hK'').inv (D.quotientFibreIso k K K' hK').inv :=
  D.quotientFibreIso_inv_comp_of_factorization h k K K' K'' hK' hK'' hKm
    (D.toCoherentSituation.compComparison h k)
    (D.baseChangeComparison_comp_compComparison hc h k)

/-! ### The morphisms of `Coh_{X/B}` attached to an identification of pulled-back quotients -/

/-- **The action of the morphism `Quot_{F/X/B} ⟶ Coh_{X/B}` on a morphism of test schemes
together with an identification of the pulled-back kernel.**  Its base map is the given morphism
of test schemes and its module comparison is
`AlgebraicGeometry.Space.QuotSituation.quotientFibreIso`.

For the pulled-back kernel itself this is `AlgebraicGeometry.Space.QuotSituation.cohHom`. -/
@[implicit_reducible]
def cohHomOfData {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {K : Subobject (D.baseChangeModule T)} {K' : Subobject (D.baseChangeModule T')}
    (hK : D.quotientPullback h K = K')
    (hmem : K ∈ D.properlySupportedQuotients T)
    (hmem' : K' ∈ D.properlySupportedQuotients T') :
    CoherentHom (D.cohObject T' K' hmem') (D.cohObject T K hmem) where
  base := h
  fibre := (D.quotientFibreIso h K K' hK).inv
  isIso_fibre := Iso.isIso_inv _

/-- The base map of that morphism is the given morphism of test schemes. -/
theorem cohHomOfData_base {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {K : Subobject (D.baseChangeModule T)} {K' : Subobject (D.baseChangeModule T')}
    (hK : D.quotientPullback h K = K')
    (hmem : K ∈ D.properlySupportedQuotients T)
    (hmem' : K' ∈ D.properlySupportedQuotients T') :
    (D.cohHomOfData h hK hmem hmem').base = h :=
  rfl

/-- The module comparison of that morphism is
`AlgebraicGeometry.Space.QuotSituation.quotientFibreIso`. -/
theorem cohHomOfData_fibre {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {K : Subobject (D.baseChangeModule T)} {K' : Subobject (D.baseChangeModule T')}
    (hK : D.quotientPullback h K = K')
    (hmem : K ∈ D.properlySupportedQuotients T)
    (hmem' : K' ∈ D.properlySupportedQuotients T') :
    (D.cohHomOfData h hK hmem hmem').fibre = (D.quotientFibreIso h K K' hK).inv :=
  rfl

/-- **Stacks 0DP6, the composition law for the morphism `Quot_{F/X/B} ⟶ Coh_{X/B}`.**  The
morphism attached to a morphism of test schemes which is a composite `h ≫ k`, together with any
identification of the kernel pulled back along it, is the composite in `Coh_{X/B}` of the
morphisms attached to `h` and to `k`. -/
theorem cohHomOfData_comp (hc : ModulePushforwardCoherence B S hS)
    {T'' T' T : SchemesOver D.Y} (h : T'' ⟶ T') (k : T' ⟶ T) (m : T'' ⟶ T) (hm : m = h ≫ k)
    {K : Subobject (D.baseChangeModule T)} {K' : Subobject (D.baseChangeModule T')}
    {K'' : Subobject (D.baseChangeModule T'')}
    (hK' : D.quotientPullback k K = K') (hK'' : D.quotientPullback h K' = K'')
    (hKm : D.quotientPullback m K = K'')
    (hmem : K ∈ D.properlySupportedQuotients T)
    (hmem' : K' ∈ D.properlySupportedQuotients T')
    (hmem'' : K'' ∈ D.properlySupportedQuotients T'') :
    D.cohHomOfData m hKm hmem hmem'' =
      CoherentHom.comp (D.cohHomOfData h hK'' hmem' hmem'')
        (D.cohHomOfData k hK' hmem hmem') := by
  subst hm
  refine coherentHom_eq_of_heq rfl (heq_of_eq ?_)
  rw [D.cohHomOfData_fibre, CoherentHom.comp_fibre, D.cohHomOfData_fibre,
    D.cohHomOfData_fibre]
  exact D.quotientFibreIso_inv_comp hc h k K K' K'' hK' hK'' hKm

/-! ### `Quot_{F/X/B}` as a category fibred in groupoids, and the object assignment -/

/-- **The object of `Coh_{X/B}` attached to a section of the Quot presheaf.**  A quotient over a
scheme `T` of the site consists of a morphism `T ⟶ B` and a quotient of `F_T` over the resulting
test scheme, and `AlgebraicGeometry.Space.QuotSituation.cohObject` turns the latter into an
object of `Coh_{X/B}`. -/
def cohObjectOfFamily {T : BigFppfOver B S hS} (x : QuotFamilyOver D T) :
    CoherentObject D.toCoherentSituation :=
  D.cohObject (CostructuredArrow.mk x.toBase) x.subobject x.mem

/-- **The morphism of test schemes over `B` attached to a morphism of the category of elements of
the Quot presheaf.**  A morphism of that category is a morphism `g : T' ⟶ T` of schemes of the
site together with an identification of the section over `T'` with the restriction of the section
over `T`; in particular the two morphisms to `B` agree after composing with `g`, which is exactly
what makes `g` a morphism of test schemes over `B`. -/
def familyBaseMap {T' T : BigFppfOver B S hS} (g : T' ⟶ T) (y : QuotFamilyOver D T)
    {x : QuotFamilyOver D T'} (hx : x = y.baseChange g) :
    (CostructuredArrow.mk x.toBase : SchemesOver D.Y) ⟶ CostructuredArrow.mk y.toBase :=
  CostructuredArrow.homMk g (congrArg QuotFamilyOver.toBase hx).symm

/-- **The kernel of a restricted section is the pulled-back kernel.**  Restriction in the Quot
presheaf pulls the kernel back along
`AlgebraicGeometry.Space.QuotSituation.familyBaseMap`. -/
theorem quotientPullback_familyBaseMap {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (y : QuotFamilyOver D T) {x : QuotFamilyOver D T'} (hx : x = y.baseChange g) :
    D.quotientPullback (D.familyBaseMap g y hx) y.subobject = x.subobject := by
  subst hx
  rfl

/-- **`Quot_{F/X/B}` as a category fibred in groupoids over the big fppf site of `S`**: the
category of elements of the Quot presheaf of Stacks 09TR, read through Stacks 0049 as a category
over the site, which is fibred in groupoids with discrete fibres. Its hom-sets lie in the
universe of those of `Coh_{X/B}`. -/
def quotCatFiberedInGroupoids :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (presheafOfGroupoids (D.quotSitePresheaf ⋙ typeToGrpd))
    (isFiberedInGroupoids_presheafOfGroupoids _)

end QuotSituation

end AlgebraicGeometry.Space

end
