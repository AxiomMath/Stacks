module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalIdealRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsFunctorial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal sequence on the corepresenting sheaves of differentials

Let `R ⟶ A ⟶ B` be morphisms of sheaves of commutative rings on a site `(C, J)` with `A ⟶ B`
locally surjective. `Stacks.Sites.Conormal.conormalSequence` realises the conormal sequence
in the *image-presheaf model*, where the middle and right terms are sheafifications of
objectwise constructions. This file transports it onto the sheaves of relative differentials
that corepresent the derivations functor, which are the objects Stacks 08TR works with: the
middle term becomes the extension of scalars along `A ⟶ B` of `Ω_{A/R}` and the right term
becomes `Ω_{B/R}`.

The transport is forced rather than chosen. Both the image-presheaf model of `Ω_{B/R}` and the
image-presheaf model of `B ⊗_A Ω_{A/R}` are shown to corepresent the same functors as their
corepresenting counterparts, so the comparison isomorphisms exist and are unique once their
effect on local differentials is prescribed.

## Main definitions

* `Stacks.Sites.Conormal.imageDifferentialsIso`: the image-presheaf model of `Ω_{B/R}` agrees
  with the corepresenting sheaf of relative differentials.
* `Stacks.Sites.Conormal.tensorDifferentialsIso`: the image-presheaf model of
  `B ⊗_A Ω_{A/R}` agrees with the extension of scalars of the corepresenting sheaf.
* `Stacks.Sites.Conormal.differentialSequence`: the conormal sequence with its middle and
  right terms expressed by the corepresenting sheaves of differentials. This is the sequence
  of [Stacks 08TS]; its leftmost term is the conormal sheaf `I/I²`, identified as such by
  `Stacks.Sites.Conormal.differentialSequence_X₁_desc_unique`.
* `Stacks.Sites.Conormal.sectionsLeibnizDerivation`: a family of maps on the sections of `A`
  which is additive, satisfies the Leibniz rule over `φ` and kills the sections of `R`, read
  as a derivation of `A` with values in a sheaf of `B`-modules.
* `Stacks.Sites.Conormal.tensorDifferentialsDesc`: **the sheaf-level descent out of the middle
  term** `B ⊗_A Ω_{A/R}`, the morphism such a family classifies. This is the counterpart of
  the ring-level `Stacks.NaiveCotangent.cotangentSpaceDesc`.

## Main results

* `Stacks.Sites.Conormal.differentialSequence_exact` and
  `Stacks.Sites.Conormal.differentialSequence_epi`: the transported sequence is exact at its
  middle term and its right-hand map is an epimorphism.
* `Stacks.Sites.Conormal.differentialSequence_f_class` and
  `Stacks.Sites.Conormal.differentialSequence_f_unique`: the left-hand map carries the
  conormal class of a local section of the kernel to the adjunction-unit image of its
  universal differential, and that formula determines it.
* `Stacks.Sites.Conormal.differentialSequence_g_differential`: the right-hand map carries
  that element to the universal differential of the image section.
* `Stacks.Sites.Conormal.differentialSequence_g_eq_mapDifferentials`: under the
  extension/restriction of scalars adjunction, the right-hand map is exactly the canonical
  map on relative differentials of Stacks 08TR attached to the square `R → A → B`.
* `Stacks.Sites.Conormal.differentialSequence_X₁_hom_ext` and
  `Stacks.Sites.Conormal.differentialSequence_X₁_desc_unique`: the leftmost term is `I/I²`,
  by its universal property — an `O₂`-linear natural family of maps out of the kernel ideal
  descends to it uniquely, by the rule `f mod I² ↦ ρ f`.
* `Stacks.Sites.Conormal.tensorSheaf_hom_ext`: two morphisms out of the middle term agreeing
  on the local sections `1 ⊗ d f` are equal.
* `Stacks.Sites.Conormal.tensorDifferentialsDesc_tensorDifferential` and
  `Stacks.Sites.Conormal.tensorDifferentialsDesc_unique`: the descent takes the prescribed
  value on each local section `1 ⊗ d x`, and is the only morphism that does. Together they
  say that a derivation out of `B ⊗_A Ω_{A/R}` is determined by, and constructible from, its
  values on the sections of `A`.
* `Stacks.Sites.Conormal.conormalSequence_f_comp_tensorDifferentialsDesc`: a morphism out of
  the conormal sheaf induced by such a family factors through the middle term, the
  factorisation being the descent. This is what kills a coboundary in `Ext¹`.
* `Stacks.Sites.Conormal.isIso_cokernel_map_conormalSequence_f`: a change of presentation
  induces an isomorphism on the cokernels of the two conormal maps, both being `Ω_{B/R}`.

## Implementation notes

The source writes the middle term's local sections as `d f ⊗ 1`. Rather than choose a model
of the tensor product, that element is expressed as the image of the universal differential
`d f` under the unit of the extension/restriction of scalars adjunction, which is what pins
down both comparison isomorphisms.

Extension of scalars on *presheaves* of modules is not available from the library at the
universe needed here, so it is built by hand (`scalarExtensionPresheaf` and
`scalarExtensionPresheafAdjunction`); its only role is to supply the right adjoint instance
that `SheafOfModules.pullback` needs.

The two comparison isomorphisms are obtained from `Classical.choose` applied to an existence
statement that already carries the formula on local differentials. This keeps the formula
available as a theorem about the isomorphism itself rather than about a particular
construction of it.

### Derivation descent, and the kernel-ideal form consumers want

`Stacks.Sites.Conormal.quotientDerivationEquiv` is the **descent of a derivation along the
locally surjective `φ : A ⟶ B`**: derivations out of `B` are the same as derivations out of the
objectwise quotient `quotientPresheaf φ = A/ker φ`. It and the chain building it
(`restrictQuotientDerivation`, `extendQuotientDerivation` and their lemmas) were `private` until
this was noticed; they are public now because they are the only statement of derivation descent
in the library, and consumers outside this file need them. The gluing step they rest on is
`Stacks.SheafOfModules.exists_derivation_of_locallyBijective` of
`StacksFrontier/CategoryTheory/Sites/Modules/InternalHomAndFlatness/NaiveCotangentExtClass.lean`,
public for the same reason.

What is **not** here is the restatement consumers actually ask for, namely

> derivations of `A` into `N` that annihilate `ker φ` are the same as derivations of `B` into `N`,

which is `quotientDerivationEquiv` composed with one further equivalence: derivations out of
`A/ker φ` are the derivations out of `A` killing `ker φ`. That step is elementary in the
forward direction — precompose with `toQuotient φ.hom`, which is objectwise
`Ideal.Quotient.mk`, and a derivation so obtained kills `kernelIdeal φ` because `mk` does — and
needs objectwise `Ideal.Quotient.lift` for the inverse. Its one point of friction is that the
two sides restrict scalars differently: the quotient side along
`quotientToRingSheaf J A B φ`, the `A` side along `A ⟶ B`, so identifying them wants a
composition coherence for `PresheafOfModules.restrictScalars` along `A ⟶ A/ker φ ⟶ B`.

The consumer this matters to was exactness at the middle term of the conormal sequence of
Stacks 05ZA for algebraic spaces.  That clause is proved, at immersion generality, by
`AlgebraicGeometry.Space.conormalSequenceOfImmersion_exact` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceImmersionKernelExactness.lean`, and the
route it took is the one the "What is not proved" section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceDifferentials.lean` records; this step is
not on it.

The whole chain ending in `quotientDerivationEquiv` is public, not only that equivalence. A
public body may not reference a private declaration, so exposing the equivalence alone does not
compile under the module system. The breadth
here is therefore forced, and re-privatizing any single link would break the build rather than
tidy it.

Sheafification of abelian groups on an essentially small site, and its inverting the locally
bijective maps, are `AlgebraicGeometry.SheafOfModules.siteHasSheafify` and
`AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective` of
`StacksFrontier/CategoryTheory/Sites/Modules/Differentials.lean`, taken as the local instances
below; they transfer the two facts from a small model of the site.

## References

* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS)
* [Stacks Project, Tag 08TR](https://stacks.math.columbia.edu/tag/08TR), the canonical map
  on relative differentials attached to a commutative square.
-/

@[expose] public section

open CategoryTheory TensorProduct

universe v u w z v₁ u₁

namespace Stacks.Sites.Conormal

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite moduleOfDifferentialsOfSite
  universalDerivationOfSite derivationsFunctor mapDifferentials functorialDifferentials
  DifferentialsMapData descentFun descentFun_comp descentFun_naturality)

-- `Stacks.SheafOfModules.Tensor.ringSheaf` unfolds to `sheafCompose`, whose action on objects is a
-- structure instance; without this, instance search cannot see that the sections of the
-- underlying sheaf of rings are the sections of the sheaf of commutative rings, and the
-- scalar action of `B` on a sheaf of `B`-modules is not found.
attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (R A B : Sheaf J CommRingCat.{w}) (a : R ⟶ A) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective J φ.hom]

/-- On an essentially small site, sheafification of presheaves of abelian groups exists. -/
local instance [EssentiallySmall.{z} C] : HasSheafify J AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify (J := J)

/-- On an essentially small site, the morphisms of presheaves of abelian groups inverted by
sheafification are precisely the locally bijective ones. -/
local instance [EssentiallySmall.{z} C] : J.WEqualsLocallyBijective AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective (J := J)

section ImageDifferentials

/-- A derivation out of `B`, restricted along the structure map of the image presheaf. -/
private noncomputable def restrictQuotientDerivation
    (N : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))
    (D : N.val.Derivation' (a ≫ φ).hom) :
    ((PresheafOfModules.restrictScalars (quotientToRingSheaf J A B φ)).obj
      N.val).Derivation' (a.hom ≫ toQuotient φ.hom) where
  d {X} := (D.d (X := X)).comp ((quotientToTarget φ.hom).app X).hom.toAddMonoidHom
  d_mul {X} x y := by
    change D.d ((quotientToTarget φ.hom).app X (x * y)) = _
    rw [map_mul, D.d_mul]
    rfl
  d_map {X Y} f x := by
    change D.d ((quotientToTarget φ.hom).app Y ((quotientPresheaf φ.hom).map f x)) = _
    rw [(quotientToTarget φ.hom).naturality_apply f x]
    exact D.d_map f _
  d_app {X} x := by
    change D.d ((quotientToTarget φ.hom).app X ((a.hom ≫ toQuotient φ.hom).app X x)) = 0
    change D.d ((a ≫ φ).hom.app X x) = 0
    exact D.d_app x

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- A derivation out of `B` is determined by its values on sections coming from the image
presheaf, because those cover. -/
private theorem quotientDerivation_ext_of_image
    (N : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))
    (D E : N.val.Derivation' (a ≫ φ).hom)
    (h : ∀ X b, D.d ((quotientToTarget φ.hom).app X b) =
      E.d ((quotientToTarget φ.hom).app X b)) : D = E := by
  ext X x
  let S := Presheaf.imageSieve (quotientToTarget φ.hom) x
  have hS : S ∈ J X.unop := Presheaf.imageSieve_mem J (quotientToTarget φ.hom) x
  apply N.isSheaf.isSeparated X.unop S hS
  intro Y k hk
  obtain ⟨b, hb⟩ := hk
  show (N.val.map k.op).hom (D.d x) = (N.val.map k.op).hom (E.d x)
  have key : D.d (B.obj.map k.op x) = E.d (B.obj.map k.op x) := by
    rw [← hb]
    exact h _ _
  exact (D.d_map k.op x).symm.trans (key.trans (E.d_map k.op x))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Restriction along the structure map of the image presheaf is injective on derivations out of
`B`, by `quotientDerivation_ext_of_image`. -/
private theorem restrictQuotientDerivation_injective
    (N : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))
    (D E : N.val.Derivation' (a ≫ φ).hom)
    (h : restrictQuotientDerivation.{v, u, w, z} J R A B a φ N D =
      restrictQuotientDerivation.{v, u, w, z} J R A B a φ N E) : D = E := by
  apply quotientDerivation_ext_of_image J R A B a φ N D E
  intro X b
  exact congrArg (fun d ↦ d.d (X := X) b) h

/-- The structure map of the image presheaf, on underlying types. -/
private noncomputable abbrev quotientTypesMap :=
  Functor.whiskerRight (quotientToTarget φ.hom) (forget CommRingCat.{w})

variable (N : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The underlying type-valued presheaf of a sheaf of modules is a sheaf. -/
private lemma isSheaf_moduleTypes :
    Presheaf.IsSheaf J (N.val.presheaf ⋙ forget AddCommGrpCat.{max w u v z}) :=
  ((sheafCompose J (forget AddCommGrpCat.{max w u v z})).obj
    ((_root_.SheafOfModules.toSheaf.{max w u v z} _).obj N)).property

/-- A derivation of the image presheaf, descended to a family of maps on sections of `B`. -/
private noncomputable def extendedQuotientDerivationTypes
    (D : ((PresheafOfModules.restrictScalars (quotientToRingSheaf J A B φ)).obj
      N.val).Derivation' (a.hom ≫ toQuotient φ.hom)) (X : Cᵒᵖ) :
    B.obj.obj X → N.val.obj X :=
  descentFun (H := N.val.presheaf ⋙ forget AddCommGrpCat) J (quotientTypesMap J A B φ)
    (isSheaf_moduleTypes J B N) (fun _ x ↦ D.d x) (fun k x ↦ D.d_map k x) X

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The descended family of maps agrees with the given derivation on sections coming from the
image presheaf.  This is the defining equation of `extendedQuotientDerivationTypes`. -/
private lemma extendedQuotientDerivationTypes_image
    (D : ((PresheafOfModules.restrictScalars (quotientToRingSheaf J A B φ)).obj
      N.val).Derivation' (a.hom ≫ toQuotient φ.hom)) (X : Cᵒᵖ)
    (x : (quotientPresheaf φ.hom).obj X) :
    extendedQuotientDerivationTypes J R A B a φ N D X
      ((quotientToTarget φ.hom).app X x) = D.d x :=
  descentFun_comp (H := N.val.presheaf ⋙ forget AddCommGrpCat) J (quotientTypesMap J A B φ)
    (isSheaf_moduleTypes J B N) (fun _ x ↦ D.d x) (fun k x ↦ D.d_map k x) X x

/-- Every derivation of the image presheaf extends uniquely to a derivation out of `B`. -/
private noncomputable def extendQuotientDerivation
    (D : ((PresheafOfModules.restrictScalars (quotientToRingSheaf J A B φ)).obj
      N.val).Derivation' (a.hom ≫ toQuotient φ.hom)) :
    N.val.Derivation' (a ≫ φ).hom := by
  let e := extendedQuotientDerivationTypes J R A B a φ N D
  have he (X : Cᵒᵖ) (x : (quotientPresheaf φ.hom).obj X) :
      e X ((quotientToTarget φ.hom).app X x) = D.d x :=
    extendedQuotientDerivationTypes_image J R A B a φ N D X x
  have hn {X Y : Cᵒᵖ} (k : X ⟶ Y) (x : B.obj.obj X) :
      e Y (B.obj.map k x) = N.val.map k (e X x) :=
    descentFun_naturality (H := N.val.presheaf ⋙ forget AddCommGrpCat) J
      (quotientTypesMap J A B φ) (isSheaf_moduleTypes J B N) (fun _ x ↦ D.d x)
      (fun k x ↦ D.d_map k x) k x
  refine
    { d := AddMonoidHom.mk' (fun x ↦ e _ x) ?_
      d_mul := ?_
      d_map := hn
      d_app := ?_ }
  · intro x y
    rename_i X
    apply N.isSheaf.isSeparated X.unop _
      (J.intersection_covering
        (Presheaf.imageSieve_mem J (quotientToTarget φ.hom) x)
        (Presheaf.imageSieve_mem J (quotientToTarget φ.hom) y))
    rintro Y k ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    change N.val.map k.op (e X (x + y)) = N.val.map k.op (e X x + e X y)
    rw [map_add, ← hn, ← hn, ← hn, map_add, ← hs, ← ht, ← map_add, he, he, he]
    exact map_add D.d s t
  · intro X x y
    apply N.isSheaf.isSeparated X.unop _
      (J.intersection_covering
        (Presheaf.imageSieve_mem J (quotientToTarget φ.hom) x)
        (Presheaf.imageSieve_mem J (quotientToTarget φ.hom) y))
    rintro Y k ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    change N.val.map k.op (e X (x * y)) = N.val.map k.op (x • e X y + y • e X x)
    rw [map_add,
      show (N.val.map k.op (x • e X y) : N.val.obj (Opposite.op Y)) =
          B.obj.map k.op x • e _ (B.obj.map k.op y) from
        (by rw [hn]; exact N.val.map_smul k.op x (e X y)),
      show (N.val.map k.op (y • e X x) : N.val.obj (Opposite.op Y)) =
          B.obj.map k.op y • e _ (B.obj.map k.op x) from
        (by rw [hn]; exact N.val.map_smul k.op y (e X x)),
      ← hn]
    change e _ (B.obj.map k.op (x * y)) =
      B.obj.map k.op x • e _ (B.obj.map k.op y) + B.obj.map k.op y • e _ (B.obj.map k.op x)
    rw [map_mul, ← hs, ← ht, ← map_mul, he, he, he]
    exact D.d_mul s t
  · intro X x
    change e X ((a ≫ φ).hom.app X x) = 0
    change e X ((quotientToTarget φ.hom).app X ((a.hom ≫ toQuotient φ.hom).app X x)) = 0
    rw [he]
    exact D.d_app x

/-- Derivations out of `B` are the same as derivations of the image presheaf.

This is the descent of a derivation along the locally surjective `φ : A ⟶ B`.  It is stated at
the objectwise quotient `quotientPresheaf φ = A/ker φ`; the form consumers ask for, a derivation
of `A` annihilating `ker φ`, is one further step away — see the note on the kernel-ideal
restatement in the module docstring. -/
private noncomputable def quotientDerivationEquiv :
    N.val.Derivation' (a ≫ φ).hom ≃
      ((PresheafOfModules.restrictScalars (quotientToRingSheaf J A B φ)).obj
        N.val).Derivation' (a.hom ≫ toQuotient φ.hom) where
  toFun := restrictQuotientDerivation J R A B a φ N
  invFun := extendQuotientDerivation J R A B a φ N
  left_inv D := by
    apply restrictQuotientDerivation_injective J R A B a φ N
    ext X x
    exact extendedQuotientDerivationTypes_image J R A B a φ N _ X x
  right_inv D := by
    ext X x
    exact extendedQuotientDerivationTypes_image J R A B a φ N D X x

end ImageDifferentials

section LiftedDifferentials

variable {S T : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The universal derivation of the objectwise Kähler differentials, after the universe
lift. -/
private noncomputable def liftedDifferentialDerivation (b : S ⟶ T) :
    ((liftModules.{v, u, w, z} _).obj
      (differentialsPresheaf b)).Derivation' b where
  d {X} := (ULift.moduleEquiv (R := T.obj X)).symm.toLinearMap.toAddMonoidHom.comp
    (PresheafOfModules.DifferentialsConstruction.derivation' b).d
  d_mul x y := by
    change ULift.up (_) = ULift.up (_)
    congr 1
    exact (PresheafOfModules.DifferentialsConstruction.derivation' b).d_mul x y
  d_map f x := by
    change ULift.up (_) = ULift.up (_)
    congr 1
    exact (PresheafOfModules.DifferentialsConstruction.derivation' b).d_map f x
  d_app x := by
    change ULift.up (_) = ULift.up 0
    congr 1
    exact (PresheafOfModules.DifferentialsConstruction.derivation' b).d_app x

/-- The universe lift of the objectwise differentials, as an isomorphism of modules over the
sections of the target. Naming it fixes the implicit arguments, so that the component maps
below and the formula they satisfy are stated with the same instances. -/
private noncomputable abbrev liftedDifferentialEquiv (b : S ⟶ T) (X : Cᵒᵖ) :
    ULift.{max u v z} (CommRingCat.KaehlerDifferential (b.app X)) ≃ₗ[T.obj X]
      CommRingCat.KaehlerDifferential (b.app X) :=
  ULift.moduleEquiv

private lemma liftedDifferentialApp_hom_ext.{w', t} {S T : CommRingCat.{w'}} (b : S ⟶ T)
    (N : ModuleCat.{max w' t} T)
    (f g : ModuleCat.of T (ULift.{t} (CommRingCat.KaehlerDifferential b)) ⟶ N)
    (h : ∀ x, f (ULift.up (CommRingCat.KaehlerDifferential.d x)) =
      g (ULift.up (CommRingCat.KaehlerDifferential.d x))) : f = g := by
  let := b.hom.toAlgebra
  let := Module.compHom (N : Type (max w' t)) b.hom
  let : IsScalarTower S T N := IsScalarTower.of_compHom S T N
  have hh : f.hom.comp ULift.moduleEquiv.symm.toLinearMap =
      g.hom.comp ULift.moduleEquiv.symm.toLinearMap := by
    apply Derivation.liftKaehlerDifferential_unique
    ext y
    exact h y
  ext x
  exact LinearMap.congr_fun hh x.down

private lemma liftedDifferential_hom_ext (b : S ⟶ T)
    (N : PresheafOfModules.{max w u v z} (T ⋙ forget₂ _ RingCat))
    (f g : (liftModules.{v, u, w, z} _).obj (differentialsPresheaf b) ⟶ N)
    (h : ∀ X x, f.app X (ULift.up (CommRingCat.KaehlerDifferential.d x)) =
      g.app X (ULift.up (CommRingCat.KaehlerDifferential.d x))) : f = g := by
  ext X : 1
  exact liftedDifferentialApp_hom_ext.{w, max u v z} (b.app X) (N.obj X)
    (f.app X) (g.app X) (h X)

/-- On sections, the morphism out of the lifted differentials presheaf determined by a
derivation. -/
private noncomputable def liftedDifferentialDescApp (b : S ⟶ T)
    (N : PresheafOfModules.{max w u v z} (T ⋙ forget₂ _ RingCat))
    (D : N.Derivation' b) (X : Cᵒᵖ) :
    ((liftModules.{v, u, w, z} _).obj (differentialsPresheaf b)).obj X ⟶ N.obj X := by
  letI := (b.app X).hom.toAlgebra
  letI := Module.compHom (N.obj X) (b.app X).hom
  letI : IsScalarTower (S.obj X) (T.obj X) (N.obj X) :=
    IsScalarTower.of_compHom (S.obj X) (T.obj X) (N.obj X)
  exact ModuleCat.ofHom ((D.app X).liftKaehlerDifferential.comp
    (liftedDifferentialEquiv.{v, u, w, z} b X).toLinearMap)

private lemma liftedDifferentialDescApp_d (b : S ⟶ T)
    (N : PresheafOfModules.{max w u v z} (T ⋙ forget₂ _ RingCat))
    (D : N.Derivation' b) (X : Cᵒᵖ) (x : T.obj X) :
    liftedDifferentialDescApp.{v, u, w, z} b N D X
      (ULift.up (CommRingCat.KaehlerDifferential.d x)) = D.d x :=
  let := (b.app X).hom.toAlgebra
  let := Module.compHom (N.obj X) (b.app X).hom
  let : IsScalarTower (S.obj X) (T.obj X) (N.obj X) :=
    IsScalarTower.of_compHom (S.obj X) (T.obj X) (N.obj X)
  (D.app X).liftKaehlerDifferential_comp_D x

/-- The morphism out of the lifted differentials presheaf determined by a derivation. -/
private noncomputable def liftedDifferentialDesc (b : S ⟶ T)
    (N : PresheafOfModules.{max w u v z} (T ⋙ forget₂ _ RingCat))
    (D : N.Derivation' b) :
    (liftModules.{v, u, w, z} _).obj (differentialsPresheaf b) ⟶ N where
  app X := liftedDifferentialDescApp.{v, u, w, z} b N D X
  naturality {X Y} k := by
    apply liftedDifferentialApp_hom_ext.{w, max u v z} (b.app X)
    intro x
    have hd : (((liftModules.{v, u, w, z} _).obj (differentialsPresheaf b)).map k)
        (ULift.up (CommRingCat.KaehlerDifferential.d x)) =
        ULift.up (CommRingCat.KaehlerDifferential.d (T.map k x)) :=
      congrArg ULift.up
        (PresheafOfModules.DifferentialsConstruction.relativeDifferentials'_map_d b k x)
    change liftedDifferentialDescApp.{v, u, w, z} b N D Y
        ((((liftModules.{v, u, w, z} _).obj (differentialsPresheaf b)).map k)
          (ULift.up (CommRingCat.KaehlerDifferential.d x))) =
      N.map k (liftedDifferentialDescApp.{v, u, w, z} b N D X
        (ULift.up (CommRingCat.KaehlerDifferential.d x)))
    refine Eq.trans
      (congrArg (fun y ↦ liftedDifferentialDescApp.{v, u, w, z} b N D Y y) hd) ?_
    refine Eq.trans (liftedDifferentialDescApp_d.{v, u, w, z} b N D Y (T.map k x)) ?_
    exact (D.d_map k x).trans (congrArg (fun y ↦ N.map k y)
      (liftedDifferentialDescApp_d.{v, u, w, z} b N D X x).symm)

/-- The lifted differentials presheaf corepresents derivations. -/
private noncomputable def liftedDifferentialHomEquiv (b : S ⟶ T)
    (N : PresheafOfModules.{max w u v z} (T ⋙ forget₂ _ RingCat)) :
    ((liftModules.{v, u, w, z} _).obj (differentialsPresheaf b) ⟶ N) ≃ N.Derivation' b where
  toFun f := (liftedDifferentialDerivation.{v, u, w, z} b).postcomp f
  invFun := liftedDifferentialDesc.{v, u, w, z} b N
  left_inv f := by
    apply liftedDifferential_hom_ext b N
    intro X x
    exact liftedDifferentialDescApp_d.{v, u, w, z} b N _ X x
  right_inv D := by
    ext X x
    exact liftedDifferentialDescApp_d.{v, u, w, z} b N D X x

end LiftedDifferentials

section ImageDifferentialsIso

/-- Morphisms out of the image-presheaf model of `Ω_{B/R}` are derivations. -/
private noncomputable def imageDifferentialsHomEquiv
    (N : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :
    (imageDifferentialsSheaf.{v, u, w, z} J R A B a φ ⟶ N) ≃
      N.val.Derivation' (a ≫ φ).hom :=
  (PresheafOfModules.sheafificationHomEquiv.{max w u v z}
    (quotientToRingSheaf J A B φ)).trans
      ((liftedDifferentialHomEquiv.{v, u, w, z} (a.hom ≫ toQuotient φ.hom) _).trans
        (quotientDerivationEquiv J R A B a φ N).symm)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
private lemma imageDifferentialsHomEquiv_d
    (N : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))
    (f : imageDifferentialsSheaf.{v, u, w, z} J R A B a φ ⟶ N)
    (X : Cᵒᵖ) (x : (quotientPresheaf φ.hom).obj X) :
    (imageDifferentialsHomEquiv J R A B a φ N f).d
      ((quotientToTarget φ.hom).app X x) =
        f.val.app X (quotientDifferential.{v, u, w, z} J R A B a φ X x) :=
  extendedQuotientDerivationTypes_image J R A B a φ N _ X x

private noncomputable def imageDifferentialsCorepresentation :
    (derivationsFunctor.{z} R B (a ≫ φ)).CorepresentableBy
      (imageDifferentialsSheaf.{v, u, w, z} J R A B a φ) where
  homEquiv := imageDifferentialsHomEquiv J R A B a φ _
  homEquiv_comp {N N'} g f := by
    apply restrictQuotientDerivation_injective J R A B a φ N'
    ext X x
    change (imageDifferentialsHomEquiv J R A B a φ N' (f ≫ g)).d
        ((quotientToTarget φ.hom).app X x) =
      g.val.app X ((imageDifferentialsHomEquiv J R A B a φ N f).d
        ((quotientToTarget φ.hom).app X x))
    rw [imageDifferentialsHomEquiv_d, imageDifferentialsHomEquiv_d]
    rfl

/-- There is an isomorphism between the image-presheaf model of `Ω_{B/R}` and the sheaf of
relative differentials that corepresents derivations, carrying the differential of a local
section of the image presheaf to the universal differential of its image in `B`. -/
theorem exists_imageDifferentialsIso :
    ∃ e : imageDifferentialsSheaf.{v, u, w, z} J R A B a φ ≅
        moduleOfDifferentialsOfSite.{v, u, w, z} R B (a ≫ φ),
      ∀ (X : Cᵒᵖ) (x : A.obj.obj X), e.hom.val.app X
        (quotientDifferential.{v, u, w, z} J R A B a φ X (Ideal.Quotient.mk _ x)) =
        (universalDerivationOfSite.{v, u, w, z} R B (a ≫ φ)).d (φ.hom.app X x) := by
  refine ⟨(imageDifferentialsCorepresentation.{v, u, w, z} J R A B a φ).isoCoreprX, ?_⟩
  intro X x
  have h := (imageDifferentialsHomEquiv J R A B a φ
      (moduleOfDifferentialsOfSite.{v, u, w, z} R B (a ≫ φ))).apply_symm_apply
    (universalDerivationOfSite.{v, u, w, z} R B (a ≫ φ))
  have hd := congrArg (fun D ↦ D.d (X := X) (φ.hom.app X x)) h
  change (imageDifferentialsHomEquiv J R A B a φ _ _).d
    ((quotientToTarget φ.hom).app X (Ideal.Quotient.mk _ x)) = _ at hd
  rw [imageDifferentialsHomEquiv_d] at hd
  exact hd

/-- The image-presheaf model of `Ω_{B/R}` agrees with the sheaf of relative differentials
that corepresents the derivations functor. The source is spelled as the right-hand term of
`conormalSequence`, which is the spelling the sequence below composes with. -/
noncomputable def imageDifferentialsIso :
    (conormalSequence.{v, u, w, z} J R A B a φ).X₃ ≅
      moduleOfDifferentialsOfSite.{v, u, w, z} R B (a ≫ φ) :=
  Classical.choose (exists_imageDifferentialsIso.{v, u, w, z} J R A B a φ)

/-- The comparison with the corepresenting sheaf of differentials carries the differential of
a local section of the image presheaf to the universal differential of its image in `B`. -/
theorem imageDifferentialsIso_d (X : Cᵒᵖ) (x : A.obj.obj X) :
    ((imageDifferentialsIso.{v, u, w, z} J R A B a φ).hom.val.app X)
      (quotientDifferential.{v, u, w, z} J R A B a φ X (Ideal.Quotient.mk _ x)) =
      (universalDerivationOfSite.{v, u, w, z} R B (a ≫ φ)).d (φ.hom.app X x) :=
  Classical.choose_spec (exists_imageDifferentialsIso.{v, u, w, z} J R A B a φ) X x

end ImageDifferentialsIso

section ScalarExtension

variable {S T : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The tensor product of two semilinear maps, the first of them multiplicative, is
semilinear for the scalar action of the left factor. -/
private lemma map_smul_of_mul {R₀ R₀' : Type*} [CommRing R₀] [CommRing R₀'] {σ : R₀ →+* R₀'}
    {E : Type*} [CommRing E] [Algebra R₀ E] {E' : Type*} [CommRing E'] [Algebra R₀' E']
    {M : Type*} [AddCommGroup M] [Module R₀ M] {M' : Type*} [AddCommGroup M'] [Module R₀' M']
    (q : E →ₛₗ[σ] E') (hq : ∀ x y : E, q (x * y) = q x * q y) (p : M →ₛₗ[σ] M')
    (r : E) (x : E ⊗[R₀] M) :
    TensorProduct.map q p (r • x) = q r • TensorProduct.map q p x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => simp only [TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.map_tmul, hq]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- Two module morphisms out of an extension of scalars agreeing on pure tensors are equal. -/
private lemma scalarExtension_hom_ext {R₀ T₀ : Type*} [CommRing R₀] [CommRing T₀] [Algebra R₀ T₀]
    {M : Type*} [AddCommGroup M] [Module R₀ M] {P : ModuleCat T₀}
    (f g : ModuleCat.of T₀ (T₀ ⊗[R₀] M) ⟶ P) (h : ∀ t m, f (t ⊗ₜ m) = g (t ⊗ₜ m)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
  | tmul t m => exact h t m

/-- Extension of scalars on sections, for a morphism of presheaves of commutative rings. -/
private noncomputable def scalarExtensionObj (b : S ⟶ T)
    (M : PresheafOfModules.{max w u v z} (S ⋙ forget₂ CommRingCat.{w} RingCat.{w}))
    (X : Cᵒᵖ) : ModuleCat.{max w u v z} (T.obj X) := by
  letI : Algebra (S.obj X) (T.obj X) := (b.app X).hom.toAlgebra
  exact ModuleCat.of (T.obj X) ((T.obj X) ⊗[S.obj X] M.obj X)

private noncomputable def scalarExtensionMap (b : S ⟶ T)
    (M : PresheafOfModules.{max w u v z} (S ⋙ forget₂ CommRingCat.{w} RingCat.{w}))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    scalarExtensionObj.{v, u, w, z} b M X ⟶
      (ModuleCat.restrictScalars ((T.map f).hom)).obj
        (scalarExtensionObj.{v, u, w, z} b M Y) := by
  letI : Algebra (S.obj X) (T.obj X) := (b.app X).hom.toAlgebra
  letI : Algebra (S.obj Y) (T.obj Y) := (b.app Y).hom.toAlgebra
  let q : T.obj X →ₛₗ[(S.map f).hom] T.obj Y :=
    { toFun := (T.map f).hom
      map_add' := map_add (T.map f).hom
      map_smul' := by
        intro r x
        change (T.map f).hom ((b.app X).hom r * x) =
          (b.app Y).hom ((S.map f).hom r) * (T.map f).hom x
        rw [map_mul]
        congr 1
        exact (congrArg (fun g : S.obj X ⟶ T.obj Y => g.hom r) (b.naturality f)).symm }
  let t := TensorProduct.map q (M.restrictₛₗ f)
  exact ModuleCat.ofHom
    (X := scalarExtensionObj.{v, u, w, z} b M X)
    (Y := (ModuleCat.restrictScalars ((T.map f).hom)).obj
      (scalarExtensionObj.{v, u, w, z} b M Y))
    { toFun := t
      map_add' := map_add t
      map_smul' := fun r x =>
        map_smul_of_mul q (map_mul (T.map f).hom) (M.restrictₛₗ f) r x }

/-- Extension of scalars along a morphism of presheaves of commutative rings, on presheaves
of modules. -/
private noncomputable def scalarExtensionPresheaf (b : S ⟶ T)
    (M : PresheafOfModules.{max w u v z} (S ⋙ forget₂ CommRingCat.{w} RingCat.{w})) :
    PresheafOfModules.{max w u v z} (T ⋙ forget₂ CommRingCat.{w} RingCat.{w}) where
  obj := scalarExtensionObj.{v, u, w, z} b M
  map := scalarExtensionMap.{v, u, w, z} b M
  map_id X := by
    let : Algebra (S.obj X) (T.obj X) := (b.app X).hom.toAlgebra
    apply scalarExtension_hom_ext
    intro t m
    change (T.map (𝟙 X)) t ⊗ₜ[S.obj X]
        (show M.obj X from M.map (𝟙 X) m) = t ⊗ₜ[S.obj X] m
    apply congrArg₂ (fun t (m : M.obj X) => t ⊗ₜ[S.obj X] m)
    · exact ConcreteCategory.congr_hom (T.map_id X) t
    · exact ConcreteCategory.congr_hom (M.map_id X) m
  map_comp {X Y Z} f g := by
    let : Algebra (S.obj X) (T.obj X) := (b.app X).hom.toAlgebra
    let : Algebra (S.obj Y) (T.obj Y) := (b.app Y).hom.toAlgebra
    let : Algebra (S.obj Z) (T.obj Z) := (b.app Z).hom.toAlgebra
    apply scalarExtension_hom_ext
    intro t m
    change (T.map (f ≫ g)) t ⊗ₜ[S.obj Z] (show M.obj Z from M.map (f ≫ g) m) =
        (T.map g) (T.map f t) ⊗ₜ[S.obj Z] (show M.obj Z from M.map g (M.map f m))
    apply congrArg₂ (fun t (m : M.obj Z) => t ⊗ₜ[S.obj Z] m)
    · exact ConcreteCategory.congr_hom (T.map_comp f g) t
    · exact M.map_comp_apply f g m

/-- Extension of scalars is left adjoint to restriction of scalars, objectwise. -/
private noncomputable def scalarExtensionHomEquiv (b : S ⟶ T)
    (M : PresheafOfModules.{max w u v z} (S ⋙ forget₂ CommRingCat.{w} RingCat.{w}))
    (N : PresheafOfModules.{max w u v z} (T ⋙ forget₂ CommRingCat.{w} RingCat.{w})) :
    (scalarExtensionPresheaf.{v, u, w, z} b M ⟶ N) ≃
      (M ⟶ (PresheafOfModules.restrictScalars
        (Functor.whiskerRight b (forget₂ CommRingCat.{w} RingCat.{w}))).obj N) where
  toFun f :=
    { app X := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{w, w,
        max w u v z} (b.app X).hom (f.app X)
      naturality := by
        intro X Y k
        ext x
        let : Algebra (S.obj X) (T.obj X) := (b.app X).hom.toAlgebra
        let : Algebra (S.obj Y) (T.obj Y) := (b.app Y).hom.toAlgebra
        have h := congrArg (fun h ↦ h (1 ⊗ₜ[S.obj X] x)) (f.naturality k)
        change (f.app Y) (((T.map k).hom 1) ⊗ₜ[S.obj Y] (M.map k x)) =
          (N.map k) ((f.app X) (1 ⊗ₜ[S.obj X] x)) at h
        change (f.app Y) (1 ⊗ₜ[S.obj Y] (M.map k x)) =
          (N.map k) ((f.app X) (1 ⊗ₜ[S.obj X] x))
        simpa only [map_one] using h }
  invFun g :=
    { app X := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{w, w,
        max w u v z} (b.app X).hom (g.app X)
      naturality := by
        intro X Y k
        let : Algebra (S.obj X) (T.obj X) := (b.app X).hom.toAlgebra
        let : Algebra (S.obj Y) (T.obj Y) := (b.app Y).hom.toAlgebra
        apply scalarExtension_hom_ext
        intro t m
        let gx : N.obj X := g.app X m
        let gy : N.obj Y := g.app Y (M.map k m)
        have h := congrArg (fun h ↦ h m) (g.naturality k)
        change gy = (N.map k) gx at h
        change ((T.map k).hom t) • gy = (N.map k) (t • gx)
        rw [N.map_smul, h]
        rfl }
  left_inv := by
    intro f
    ext X x
    let : Algebra (S.obj X) (T.obj X) := (b.app X).hom.toAlgebra
    have h := (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{max w u v z, w, w}
      (X := M.obj X) (Y := N.obj X) (b.app X).hom).left_inv (f.app X)
    exact ConcreteCategory.congr_hom h x
  right_inv := by
    intro g
    ext X x
    have h := (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{max w u v z, w, w}
      (X := M.obj X) (Y := N.obj X) (b.app X).hom).right_inv (g.app X)
    exact ConcreteCategory.congr_hom h x

/-- Restriction of scalars on presheaves of modules has a left adjoint. -/
private noncomputable def scalarExtensionPresheafAdjunction (b : S ⟶ T) :
    (Adjunction.leftAdjointOfEquiv
      (G := PresheafOfModules.pushforward
        (F := 𝟭 C) (Functor.whiskerRight b (forget₂ CommRingCat.{w} RingCat.{w})))
      (fun M N => scalarExtensionHomEquiv.{v, u, w, z} b M N)
      (by
        intro M N N' g h
        ext X x
        rfl)) ⊣
      PresheafOfModules.pushforward
        (F := 𝟭 C) (Functor.whiskerRight b (forget₂ CommRingCat.{w} RingCat.{w})) :=
  Adjunction.adjunctionOfEquivLeft
    (fun M N => scalarExtensionHomEquiv.{v, u, w, z} b M N)
    (by
      intro M N N' g h
      ext X x
      rfl)

end ScalarExtension

section TensorDifferentialsIso

/-- The morphism of underlying sheaves of rings along which the middle term of the sequence
is a pullback of modules. -/
noncomputable abbrev underlyingRingHomForPullback :
    Stacks.SheafOfModules.Tensor.ringSheaf A ⟶
      ((𝟭 C).sheafPushforwardContinuous RingCat J J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf B) :=
  underlyingRingHomOfSite φ

/-- Restriction of scalars along `A ⟶ B` on sheaves of modules has a left adjoint. -/
noncomputable instance differentialPushforwardIsRightAdjoint :
    (_root_.SheafOfModules.pushforward.{max w u v z}
      (underlyingRingHomForPullback J A B φ)).IsRightAdjoint := by
  let : EssentiallySmall.{max w u v z} C := essentiallySmallSelf.{max w z, v, u} C
  let : HasSheafify J AddCommGrpCat.{max w u v z} :=
    AlgebraicGeometry.SheafOfModules.siteHasSheafify (J := J)
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z} :=
    AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective (J := J)
  let : (PresheafOfModules.pushforward.{max w u v z}
      (underlyingRingHomForPullback J A B φ).hom).IsRightAdjoint :=
    (scalarExtensionPresheafAdjunction.{v, u, w, z} φ.hom).isRightAdjoint
  infer_instance

/-- On sections, the lifted tensor presheaf is the extension of scalars of the lifted
differentials presheaf. -/
private noncomputable def liftedTensorAppIso (X : Cᵒᵖ) :
    ((liftModules.{v, u, w, z} _).obj (tensorPresheaf φ.hom a.hom)).obj X ≅
      (scalarExtensionPresheaf.{v, u, w, z} (toQuotient φ.hom)
        ((liftModules.{v, u, w, z} _).obj (differentialsPresheaf a.hom))).obj X := by
  let Q := A.obj.obj X ⧸ kernelIdeal φ.hom X
  let M := (differentialsPresheaf a.hom).obj X
  change ModuleCat.of Q (ULift.{max u v z} (Q ⊗[A.obj.obj X] M)) ≅
    ModuleCat.of Q (Q ⊗[A.obj.obj X] ULift.{max u v z} M)
  exact (ULift.moduleEquiv.trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Q Q)
      (ULift.moduleEquiv (R := A.obj.obj X) (M := M)).symm)).toModuleIso

private noncomputable def liftedTensorIso :
    (liftModules.{v, u, w, z} _).obj (tensorPresheaf φ.hom a.hom) ≅
      scalarExtensionPresheaf.{v, u, w, z} (toQuotient φ.hom)
        ((liftModules.{v, u, w, z} _).obj (differentialsPresheaf a.hom)) :=
  (PresheafOfModules.isoMk
    (fun X => (liftedTensorAppIso.{v, u, w, z} J R A B a φ X).symm) (by
      intro X Y k
      apply scalarExtension_hom_ext
      intro q ω
      rfl)).symm

/-- Morphisms out of the image-presheaf model of `B ⊗_A Ω_{A/R}` are derivations of `A`
with values in the restriction of scalars. -/
private noncomputable def tensorDifferentialsHomEquiv
    (N : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :
    (tensorDifferentialsSheaf.{v, u, w, z} J R A B a φ ⟶ N) ≃
      ((_root_.SheafOfModules.pushforward
        (underlyingRingHomForPullback J A B φ)).obj N).val.Derivation' a.hom :=
  (PresheafOfModules.sheafificationHomEquiv.{max w u v z}
    (quotientToRingSheaf J A B φ)).trans
      ((liftedTensorIso.{v, u, w, z} J R A B a φ).homFromEquiv.trans
        ((scalarExtensionHomEquiv.{v, u, w, z} (toQuotient φ.hom) _ _).trans
          (liftedDifferentialHomEquiv.{v, u, w, z} a.hom _)))

private lemma tensorDifferentialsHomEquiv_d
    (N : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))
    (f : tensorDifferentialsSheaf.{v, u, w, z} J R A B a φ ⟶ N)
    (X : Cᵒᵖ) (x : A.obj.obj X) :
    (tensorDifferentialsHomEquiv J R A B a φ N f).d x =
      f.val.app X (tensorDifferential.{v, u, w, z} J R A B a φ X x) := rfl

private noncomputable def tensorDifferentialsCorepresentation :
    ((_root_.SheafOfModules.pushforward (underlyingRingHomForPullback J A B φ)) ⋙
      derivationsFunctor.{z} R A a).CorepresentableBy
        (tensorDifferentialsSheaf.{v, u, w, z} J R A B a φ) where
  homEquiv := tensorDifferentialsHomEquiv J R A B a φ _
  homEquiv_comp g f := by
    apply PresheafOfModules.Derivation.ext
    funext X
    apply AddMonoidHom.ext
    intro x
    rfl

private noncomputable def pullbackDifferentialsCorepresentation :
    ((_root_.SheafOfModules.pushforward (underlyingRingHomForPullback J A B φ)) ⋙
      derivationsFunctor.{z} R A a).CorepresentableBy
        ((_root_.SheafOfModules.pullback (underlyingRingHomForPullback J A B φ)).obj
          (moduleOfDifferentialsOfSite.{v, u, w, z} R A a)) where
  homEquiv := ((_root_.SheafOfModules.pullbackPushforwardAdjunction
    (underlyingRingHomForPullback J A B φ)).homEquiv _ _).trans
      (derivationsFunctor.{z} R A a).corepresentableBy.homEquiv
  homEquiv_comp g f := by
    change (derivationsFunctor.{z} R A a).corepresentableBy.homEquiv
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction
        (underlyingRingHomForPullback J A B φ)).homEquiv _ _ (f ≫ g)) = _
    rw [Adjunction.homEquiv_naturality_right]
    exact (derivationsFunctor.{z} R A a).corepresentableBy.homEquiv_comp _ _

omit [Presheaf.IsLocallySurjective J φ.hom] in
private lemma pullbackDifferentialsCorepresentation_d
    (N : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))
    (f : (_root_.SheafOfModules.pullback (underlyingRingHomForPullback J A B φ)).obj
      (moduleOfDifferentialsOfSite.{v, u, w, z} R A a) ⟶ N)
    (X : Cᵒᵖ) (x : A.obj.obj X) :
    ((pullbackDifferentialsCorepresentation J R A B a φ).homEquiv f).d x =
      f.val.app X (((_root_.SheafOfModules.pullbackPushforwardAdjunction
        (underlyingRingHomForPullback J A B φ)).unit.app
          (moduleOfDifferentialsOfSite.{v, u, w, z} R A a)).val.app X
        ((universalDerivationOfSite.{v, u, w, z} R A a).d x)) := by
  show ((derivationsFunctor.{z} R A a).corepresentableBy.homEquiv _).d x = _
  rw [Functor.CorepresentableBy.homEquiv_eq]
  rfl

/-- There is an isomorphism between the image-presheaf model of `B ⊗_A Ω_{A/R}` and the
extension of scalars of the corepresenting sheaf of relative differentials, carrying the
local section `1 ⊗ d x` to the adjunction-unit image of the universal differential. -/
theorem exists_tensorDifferentialsIso :
    ∃ e : tensorDifferentialsSheaf.{v, u, w, z} J R A B a φ ≅
      (_root_.SheafOfModules.pullback (underlyingRingHomForPullback J A B φ)).obj
        (moduleOfDifferentialsOfSite.{v, u, w, z} R A a),
      ∀ (X : Cᵒᵖ) (x : A.obj.obj X), e.hom.val.app X
        (tensorDifferential.{v, u, w, z} J R A B a φ X x) =
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction
        (underlyingRingHomForPullback J A B φ)).unit.app
          (moduleOfDifferentialsOfSite.{v, u, w, z} R A a)).val.app X
        ((universalDerivationOfSite.{v, u, w, z} R A a).d x) := by
  refine ⟨(tensorDifferentialsCorepresentation.{v, u, w, z} J R A B a φ).uniqueUpToIso
    (pullbackDifferentialsCorepresentation.{v, u, w, z} J R A B a φ), ?_⟩
  intro X x
  have h : (tensorDifferentialsCorepresentation J R A B a φ).homEquiv
      ((tensorDifferentialsCorepresentation.{v, u, w, z} J R A B a φ).uniqueUpToIso
        (pullbackDifferentialsCorepresentation.{v, u, w, z} J R A B a φ)).hom =
        (pullbackDifferentialsCorepresentation J R A B a φ).homEquiv (𝟙 _) :=
    (tensorDifferentialsCorepresentation J R A B a φ).homEquiv.apply_symm_apply _
  have hx := congrArg (fun D ↦ D.d (X := X) x) h
  change (tensorDifferentialsHomEquiv J R A B a φ _ _).d x = _ at hx
  rw [tensorDifferentialsHomEquiv_d, pullbackDifferentialsCorepresentation_d] at hx
  exact hx

/-- The image-presheaf model of the middle term agrees with the extension of scalars of the
corepresenting sheaf of relative differentials. The source is spelled as the middle term of
`conormalSequence`, which is the spelling the sequence below composes with. -/
noncomputable def tensorDifferentialsIso :
    (conormalSequence.{v, u, w, z} J R A B a φ).X₂ ≅
      (_root_.SheafOfModules.pullback (underlyingRingHomForPullback J A B φ)).obj
        (moduleOfDifferentialsOfSite.{v, u, w, z} R A a) :=
  Classical.choose (exists_tensorDifferentialsIso.{v, u, w, z} J R A B a φ)

/-- The comparison carries the image-presheaf differential `1 ⊗ d x` to the source's
`d x ⊗ 1`, represented by the adjunction-unit image of the universal differential. -/
theorem tensorDifferentialsIso_d (X : Cᵒᵖ) (x : A.obj.obj X) :
    ((tensorDifferentialsIso.{v, u, w, z} J R A B a φ).hom.val.app X)
      (tensorDifferential.{v, u, w, z} J R A B a φ X x) =
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction
      (underlyingRingHomForPullback J A B φ)).unit.app
        (moduleOfDifferentialsOfSite.{v, u, w, z} R A a)).val.app X
      ((universalDerivationOfSite.{v, u, w, z} R A a).d x) :=
  Classical.choose_spec (exists_tensorDifferentialsIso.{v, u, w, z} J R A B a φ) X x

/-- The inverse comparison carries the adjunction-unit image of the universal differential of a
section of `A` back to the image-presheaf differential `1 ⊗ d x` in the middle term of
`conormalSequence`. -/
theorem tensorDifferentialsIso_inv_d (X : Cᵒᵖ) (x : A.obj.obj X) :
    ((tensorDifferentialsIso.{v, u, w, z} J R A B a φ).inv.val.app X)
      (((_root_.SheafOfModules.pullbackPushforwardAdjunction
        (underlyingRingHomForPullback J A B φ)).unit.app
          (moduleOfDifferentialsOfSite.{v, u, w, z} R A a)).val.app X
        ((universalDerivationOfSite.{v, u, w, z} R A a).d x)) =
      tensorDifferential.{v, u, w, z} J R A B a φ X x := by
  have hcmp (y : (conormalSequence.{v, u, w, z} J R A B a φ).X₂.val.obj X) :
      ((tensorDifferentialsIso.{v, u, w, z} J R A B a φ).inv.val.app X)
        (((tensorDifferentialsIso.{v, u, w, z} J R A B a φ).hom.val.app X) y) = y :=
    ConcreteCategory.congr_hom (congrArg (fun f => f.val.app X)
      (Iso.hom_inv_id (tensorDifferentialsIso.{v, u, w, z} J R A B a φ))) y
  exact (congrArg ((tensorDifferentialsIso.{v, u, w, z} J R A B a φ).inv.val.app X)
    (tensorDifferentialsIso_d J R A B a φ X x)).symm.trans (hcmp _)

end TensorDifferentialsIso

section DifferentialSequence

/-- The conormal sequence `I/I² ⟶ B ⊗_A Ω_{A/R} ⟶ Ω_{B/R} ⟶ 0`, with its middle and right
terms expressed by the sheaves of relative differentials that corepresent derivations. -/
@[stacks 08TS "the canonical exact sequence of `O'₂`-modules", stacks 08TF
  "canonical conormal sequence"]
noncomputable def differentialSequence :
    ShortComplex
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) where
  X₁ := (conormalSequence.{v, u, w, z} J R A B a φ).X₁
  X₂ := (_root_.SheafOfModules.pullback (underlyingRingHomForPullback J A B φ)).obj
    (moduleOfDifferentialsOfSite.{v, u, w, z} R A a)
  X₃ := moduleOfDifferentialsOfSite.{v, u, w, z} R B (a ≫ φ)
  f := (conormalSequence.{v, u, w, z} J R A B a φ).f ≫
    (tensorDifferentialsIso.{v, u, w, z} J R A B a φ).hom
  g := (tensorDifferentialsIso.{v, u, w, z} J R A B a φ).inv ≫
    (conormalSequence.{v, u, w, z} J R A B a φ).g ≫
    (imageDifferentialsIso.{v, u, w, z} J R A B a φ).hom
  zero := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc,
      (conormalSequence.{v, u, w, z} J R A B a φ).zero, Limits.zero_comp]

-- The sequence's terms are read off its three projections in the statements below; without
-- this the elaborator cannot see, at `implicit` transparency, that `differentialSequence.X₂`
-- is the scalar extension of `Ω_{A/R}`, and every `rw` on such a goal fails with
-- "did not find an occurrence of the pattern".
attribute [local implicit_reducible] differentialSequence

private noncomputable def differentialSequenceIso :
    conormalSequence.{v, u, w, z} J R A B a φ ≅ differentialSequence.{v, u, w, z} J R A B a φ :=
  ShortComplex.isoMk (Iso.refl _) (tensorDifferentialsIso.{v, u, w, z} J R A B a φ)
    (imageDifferentialsIso.{v, u, w, z} J R A B a φ)
    (by
      change 𝟙 _ ≫ (conormalSequence.{v, u, w, z} J R A B a φ).f ≫
        (tensorDifferentialsIso.{v, u, w, z} J R A B a φ).hom = _
      rw [Category.id_comp])
    (by
      change (tensorDifferentialsIso.{v, u, w, z} J R A B a φ).hom ≫
        (tensorDifferentialsIso.{v, u, w, z} J R A B a φ).inv ≫
        (conormalSequence.{v, u, w, z} J R A B a φ).g ≫
        (imageDifferentialsIso.{v, u, w, z} J R A B a φ).hom = _
      rw [Iso.hom_inv_id_assoc])

/-- The transported sequence is exact at the extension of scalars of `Ω_{A/R}`. -/
@[stacks 08TS "exactness at the middle term", stacks 08TF "exactness",
  sga "3 III 4.25" "exactness of (+)"]
theorem differentialSequence_exact :
    (differentialSequence.{v, u, w, z} J R A B a φ).Exact :=
  ShortComplex.exact_of_iso (differentialSequenceIso.{v, u, w, z} J R A B a φ)
    (conormalSequence_exact J R A B a φ)

/-- The transported sequence surjects onto `Ω_{B/R}`. -/
@[stacks 08TS "exactness on the right", stacks 08TF "surjectivity",
  sga "3 III 4.25" "surjectivity in (+)"]
theorem differentialSequence_epi :
    Epi (differentialSequence.{v, u, w, z} J R A B a φ).g :=
  ((ShortComplex.exact_and_epi_g_iff_of_iso
    (differentialSequenceIso.{v, u, w, z} J R A B a φ)).mp
      ⟨conormalSequence_exact J R A B a φ, inferInstance⟩).2

/-- The left-hand map carries the conormal class of a local section of the kernel to the
source's `d x ⊗ 1`. -/
@[stacks 08TS "the rule `f ↦ d f ⊗ 1` for the leftmost map", stacks 08TF
  "formula on local kernel sections"]
theorem differentialSequence_f_class (X : Cᵒᵖ) (x : kernelIdeal φ.hom X) :
    ((differentialSequence.{v, u, w, z} J R A B a φ).f.val.app X)
      (conormalClass.{v, u, w, z} J R A B a φ X x) =
      ((_root_.SheafOfModules.pullbackPushforwardAdjunction
        (underlyingRingHomForPullback J A B φ)).unit.app
          (moduleOfDifferentialsOfSite.{v, u, w, z} R A a)).val.app X
        ((universalDerivationOfSite.{v, u, w, z} R A a).d x.1) := by
  show ((tensorDifferentialsIso.{v, u, w, z} J R A B a φ).hom.val.app X)
      (((conormalSequence.{v, u, w, z} J R A B a φ).f.val.app X)
        (conormalClass.{v, u, w, z} J R A B a φ X x)) = _
  rw [conormalSequence_f_class]
  exact tensorDifferentialsIso_d J R A B a φ X x

/-- The right-hand map carries `d x ⊗ 1` to the universal differential of the image of `x`. -/
@[stacks 08TS "the right-hand map on local differentials", stacks 08TF
  "right map on differentials"]
theorem differentialSequence_g_differential (X : Cᵒᵖ) (x : A.obj.obj X) :
    ((differentialSequence.{v, u, w, z} J R A B a φ).g.val.app X)
      (((_root_.SheafOfModules.pullbackPushforwardAdjunction
        (underlyingRingHomForPullback J A B φ)).unit.app
          (moduleOfDifferentialsOfSite.{v, u, w, z} R A a)).val.app X
        ((universalDerivationOfSite.{v, u, w, z} R A a).d x)) =
      (universalDerivationOfSite.{v, u, w, z} R B (a ≫ φ)).d (φ.hom.app X x) := by
  show ((imageDifferentialsIso.{v, u, w, z} J R A B a φ).hom.val.app X)
      (((conormalSequence.{v, u, w, z} J R A B a φ).g.val.app X)
        (((tensorDifferentialsIso.{v, u, w, z} J R A B a φ).inv.val.app X)
          (((_root_.SheafOfModules.pullbackPushforwardAdjunction
            (underlyingRingHomForPullback J A B φ)).unit.app
              (moduleOfDifferentialsOfSite.{v, u, w, z} R A a)).val.app X
            ((universalDerivationOfSite.{v, u, w, z} R A a).d x)))) = _
  rw [tensorDifferentialsIso_inv_d, conormalSequence_g_differential, imageDifferentialsIso_d]

/-- Under extension/restriction of scalars, the right-hand map is exactly the canonical map
on relative differentials attached to the square `R → A → B` by Stacks 08TR. -/
@[stacks 08TS "the map on the right is the one of Stacks 08TR", stacks 08TF
  "canonical right-hand map"]
theorem differentialSequence_g_eq_mapDifferentials :
    (_root_.SheafOfModules.pullbackPushforwardAdjunction
      (underlyingRingHomForPullback J A B φ)).homEquiv
      (moduleOfDifferentialsOfSite.{v, u, w, z} R A a)
        (moduleOfDifferentialsOfSite.{v, u, w, z} R B (a ≫ φ))
        (differentialSequence.{v, u, w, z} J R A B a φ).g =
      mapDifferentials.{v, u, w, z} a (a ≫ φ) (𝟙 R) φ (by simp) := by
  let D := functorialDifferentials.{v, u, w, z} a (a ≫ φ) (𝟙 R) φ (by simp)
  apply D.unique
  ext X x
  show (((_root_.SheafOfModules.pullbackPushforwardAdjunction
      (underlyingRingHomForPullback J A B φ)).homEquiv
        (moduleOfDifferentialsOfSite.{v, u, w, z} R A a)
        (moduleOfDifferentialsOfSite.{v, u, w, z} R B (a ≫ φ))
        (differentialSequence.{v, u, w, z} J R A B a φ).g).val.app X)
      ((universalDerivationOfSite.{v, u, w, z} R A a).d x) = _
  rw [DifferentialsMapData.inducedDerivation_apply]
  rw [Adjunction.homEquiv_unit]
  show ((differentialSequence.{v, u, w, z} J R A B a φ).g.val.app X)
      (((_root_.SheafOfModules.pullbackPushforwardAdjunction
        (underlyingRingHomForPullback J A B φ)).unit.app
          (moduleOfDifferentialsOfSite.{v, u, w, z} R A a)).val.app X
        ((universalDerivationOfSite.{v, u, w, z} R A a).d x)) = _
  exact differentialSequence_g_differential J R A B a φ X x

/-- The formula on local conormal classes determines the left-hand map. -/
@[stacks 08TS "the rule `f ↦ d f ⊗ 1` characterises the leftmost map", stacks 08TF
  "uniqueness of the conormal map"]
theorem differentialSequence_f_unique
    (g : (differentialSequence.{v, u, w, z} J R A B a φ).X₁ ⟶
      (differentialSequence.{v, u, w, z} J R A B a φ).X₂)
    (hg : ∀ (X : Cᵒᵖ) (x : kernelIdeal φ.hom X),
      g.val.app X (conormalClass.{v, u, w, z} J R A B a φ X x) =
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction
          (underlyingRingHomForPullback J A B φ)).unit.app
            (moduleOfDifferentialsOfSite.{v, u, w, z} R A a)).val.app X
          ((universalDerivationOfSite.{v, u, w, z} R A a).d x.1)) :
    g = (differentialSequence.{v, u, w, z} J R A B a φ).f := by
  have h : g ≫ (tensorDifferentialsIso.{v, u, w, z} J R A B a φ).inv =
      (conormalSequence.{v, u, w, z} J R A B a φ).f := by
    apply conormalSequence_f_unique J R A B a φ
    intro X x
    show ((tensorDifferentialsIso.{v, u, w, z} J R A B a φ).inv.val.app X)
      (g.val.app X (conormalClass.{v, u, w, z} J R A B a φ X x)) = _
    rw [hg]
    exact tensorDifferentialsIso_inv_d J R A B a φ X x.1
  have h2 : (conormalSequence.{v, u, w, z} J R A B a φ).f ≫
      (tensorDifferentialsIso.{v, u, w, z} J R A B a φ).hom = g := by
    rw [← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact h2.symm

/-- **The leftmost term of the sequence is generated by the conormal classes of the local
sections of `I`**: two morphisms out of it which agree on the conormal class of every local
section of `I` are equal. Together with
`Stacks.Sites.Conormal.differentialSequence_f_class` this is what makes the rule
`f ↦ d f ⊗ 1` a characterisation of the left-hand map. -/
theorem differentialSequence_X₁_hom_ext
    (N : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))
    {g₁ g₂ : (differentialSequence.{v, u, w, z} J R A B a φ).X₁ ⟶ N}
    (h : ∀ (X : Cᵒᵖ) (x : kernelIdeal φ.hom X),
      g₁.val.app X (conormalClass.{v, u, w, z} J R A B a φ X x) =
        g₂.val.app X (conormalClass.{v, u, w, z} J R A B a φ X x)) :
    g₁ = g₂ := by
  apply sheafify_hom_ext.{v, u, w, z} J A B φ (conormalPresheaf φ.hom)
  intro X c
  obtain ⟨x, rfl⟩ := (kernelIdeal φ.hom X).toCotangent_surjective c
  exact h X x

/-- **The leftmost term of the sequence is `I/I²`.** A morphism of sheaves of `O'₂`-modules out
of it is the same thing as an `O₂`-linear natural family of maps `I(U) ⟶ N(U)` out of the
kernel ideal: every such family descends to the term, uniquely, by the rule that the conormal
class of a local section `f` of `I` goes to the value of the family at `f`. The family
annihilates `I²` automatically, a local section of `I` acting as zero on a sheaf of
`O'₂`-modules. -/
@[stacks 08TS "the leftmost term is `I/I²`, by its universal property"]
theorem differentialSequence_X₁_desc_unique
    (N : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))
    (ρ : IdealRestriction.{v, u, w, z} φ N) :
    ∃! g : (differentialSequence.{v, u, w, z} J R A B a φ).X₁ ⟶ N,
      ∀ (X : Cᵒᵖ) (x : kernelIdeal φ.hom X),
        g.val.app X (conormalClass.{v, u, w, z} J R A B a φ X x) = ρ.app X x :=
  ⟨conormalDesc.{v, u, w, z} φ N ρ,
    fun X x ↦ conormalDesc_conormalClass.{v, u, w, z} φ N R a ρ X x,
    fun _ hg ↦ differentialSequence_X₁_hom_ext.{v, u, w, z} J R A B a φ N
      (fun X x ↦ (hg X x).trans
        (conormalDesc_conormalClass.{v, u, w, z} φ N R a ρ X x).symm)⟩

end DifferentialSequence

/-! ### Cokernels of the left-hand map of an exact short complex -/

section Cokernels

variable {D : Type u₁} [Category.{v₁} D] [Abelian D]

/-- For an exact short complex whose right-hand map is an epimorphism, the right-hand term is
the cokernel of the left-hand map: the comparison morphism out of the cokernel is an
isomorphism. -/
theorem isIso_cokernelDesc_g {S : ShortComplex D} (hS : S.Exact) [Epi S.g] :
    IsIso (Limits.cokernel.desc S.f S.g S.zero) := by
  have h₁ : Limits.cokernel.desc S.f S.g S.zero ≫
      hS.desc (Limits.cokernel.π S.f) (Limits.cokernel.condition S.f) =
      𝟙 (Limits.cokernel S.f) := by
    apply (cancel_epi (Limits.cokernel.π S.f)).1
    rw [← Category.assoc, Limits.cokernel.π_desc, hS.g_desc, Category.comp_id]
  have h₂ : hS.desc (Limits.cokernel.π S.f) (Limits.cokernel.condition S.f) ≫
      Limits.cokernel.desc S.f S.g S.zero = 𝟙 S.X₃ := by
    apply (cancel_epi S.g).1
    rw [← Category.assoc, hS.g_desc, Limits.cokernel.π_desc, Category.comp_id]
  exact ⟨⟨_, h₁, h₂⟩⟩

/-- Let two exact short complexes with epimorphic right-hand maps have their right-hand terms
identified with one and the same object, compatibly with a morphism between their left-hand
maps. Then the induced morphism on the cokernels of the left-hand maps is an isomorphism. -/
theorem isIso_cokernel_map_of_g_comp_eq {S₁ S₂ : ShortComplex D}
    (h₁ : S₁.Exact) (h₂ : S₂.Exact) [Epi S₁.g] [Epi S₂.g] {Ω : D}
    (e₁ : S₁.X₃ ≅ Ω) (e₂ : S₂.X₃ ≅ Ω)
    (p : S₁.X₁ ⟶ S₂.X₁) (q : S₁.X₂ ⟶ S₂.X₂) (hpq : S₁.f ≫ q = p ≫ S₂.f)
    (hsq : q ≫ S₂.g ≫ e₂.hom = S₁.g ≫ e₁.hom) :
    IsIso (Limits.cokernel.map S₁.f S₂.f p q hpq) := by
  have : IsIso (Limits.cokernel.desc S₁.f S₁.g S₁.zero) := isIso_cokernelDesc_g h₁
  have : IsIso (Limits.cokernel.desc S₂.f S₂.g S₂.zero) := isIso_cokernelDesc_g h₂
  have hr : S₁.g ≫ e₁.hom ≫ e₂.inv = q ≫ S₂.g := by
    rw [← Category.assoc, ← hsq, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hmap := Limits.cokernel.map_desc S₁.f S₁.g S₁.zero S₂.f S₂.g S₂.zero p q
    (e₁.hom ≫ e₂.inv) hpq hr
  have hfin : Limits.cokernel.map S₁.f S₂.f p q hpq =
      (Limits.cokernel.desc S₁.f S₁.g S₁.zero ≫ e₁.hom ≫ e₂.inv) ≫
        inv (Limits.cokernel.desc S₂.f S₂.g S₂.zero) := by
    rw [← hmap, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hfin]
  infer_instance

end Cokernels

/-! ### Morphisms out of the middle term of the conormal sequence -/

section Sections

variable (N : _root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B))

/-- A morphism out of the middle term of the conormal sequence, read on the sections of the
tensor presheaf as a linear map over the image presheaf. -/
noncomputable def tensorSections
    (H : (conormalSequence.{v, u, w, z} J R A B a φ).X₂ ⟶ N) (X : Cᵒᵖ) :
    tensorObj φ.hom a.hom X →ₗ[(quotientPresheaf φ.hom).obj X]
      (ModuleCat.restrictScalars ((quotientToRingSheaf J A B φ).app X).hom).obj
        (N.val.obj X) where
  toFun t :=
    H.val.app X (toAssociatedModule.{v, u, w, z} J A B φ (tensorPresheaf φ.hom a.hom) X t)
  map_add' t t' := (congrArg (H.val.app X)
    (toAssociatedModule_add.{v, u, w, z} J A B φ (tensorPresheaf φ.hom a.hom) X t t')).trans
    (map_add (H.val.app X).hom _ _)
  map_smul' r t := (congrArg (H.val.app X)
    (toAssociatedModule_smul.{v, u, w, z} J A B φ (tensorPresheaf φ.hom a.hom) X r t)).trans
    ((H.val.app X).hom.map_smul _ _)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- On sections of the tensor presheaf, `tensorSections` is the morphism itself. -/
lemma tensorSections_apply (H : (conormalSequence.{v, u, w, z} J R A B a φ).X₂ ⟶ N)
    (X : Cᵒᵖ) (t : tensorObj φ.hom a.hom X) :
    tensorSections.{v, u, w, z} J R A B a φ N H X t =
      H.val.app X (toAssociatedModule.{v, u, w, z} J A B φ (tensorPresheaf φ.hom a.hom) X t) :=
  rfl

/-- Two morphisms out of the middle term `B ⊗[A] Ω[A/R]` of the conormal sequence which agree
on the local sections `1 ⊗ d f` are equal. -/
theorem tensorSheaf_hom_ext
    {g₁ g₂ : (conormalSequence.{v, u, w, z} J R A B a φ).X₂ ⟶ N}
    (h : ∀ (X : Cᵒᵖ) (x : A.obj.obj X),
      g₁.val.app X (tensorDifferential.{v, u, w, z} J R A B a φ X x) =
        g₂.val.app X (tensorDifferential.{v, u, w, z} J R A B a φ X x)) :
    g₁ = g₂ := by
  apply sheafify_hom_ext.{v, u, w, z} J A B φ (tensorPresheaf φ.hom a.hom)
  intro X
  have key : ∀ (H : (conormalSequence.{v, u, w, z} J R A B a φ).X₂ ⟶ N)
      (b : A.obj.obj X ⧸ kernelIdeal φ.hom X) (x : A.obj.obj X),
      tensorSections.{v, u, w, z} J R A B a φ N H X
          (b ⊗ₜ[A.obj.obj X] CommRingCat.KaehlerDifferential.d (f := a.hom.app X) x) =
        (quotientToRingSheaf J A B φ).app X b •
          H.val.app X (tensorDifferential.{v, u, w, z} J R A B a φ X x) := by
    intro H b x
    have hb : (b ⊗ₜ[A.obj.obj X] CommRingCat.KaehlerDifferential.d (f := a.hom.app X) x :
          tensorObj φ.hom a.hom X) =
        b • ((1 : A.obj.obj X ⧸ kernelIdeal φ.hom X) ⊗ₜ[A.obj.obj X]
          CommRingCat.KaehlerDifferential.d (f := a.hom.app X) x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl
    exact (congrArg (tensorSections.{v, u, w, z} J R A B a φ N H X) hb).trans
      (map_smul (tensorSections.{v, u, w, z} J R A B a φ N H X) b _)
  have hL : tensorSections.{v, u, w, z} J R A B a φ N g₁ X =
      tensorSections.{v, u, w, z} J R A B a φ N g₂ X := by
    apply tensor_hom_ext φ.hom a.hom X
    intro b x
    refine (key g₁ b x).trans (Eq.trans ?_ (key g₂ b x).symm)
    exact congrArg (fun y : N.val.obj X ↦ (quotientToRingSheaf J A B φ).app X b • y) (h X x)
  exact fun t ↦ LinearMap.congr_fun hL t

/-! ### The sheaf-level descent out of the middle term

The ring-level counterpart of what follows is `Stacks.NaiveCotangent.cotangentSpaceDesc`, the
map out of `S ⊗[P] Ω[P⁄R]` classified by an additive map satisfying the Leibniz rule.  Here the
Leibniz condition is imposed on the *presheaf sections* of `A` only, and the morphism it
classifies is defined on the sheafification: local surjectivity of `φ` forces no change of
formulation, because the middle term is the sheafification of a presheaf whose sections are a
tensor product over the image presheaf, and the sheafification unit is semilinear over the
inclusion of that image into `B`. -/

/-- **The derivation on sections determined by a family of maps satisfying the Leibniz rule.**
A family of maps on the sections of `A` which is additive, satisfies the Leibniz rule over the
presentation `φ`, kills the sections of `R` and commutes with the restriction maps is exactly a
derivation of `A` with values in `N`, the scalars of `N` restricted along `φ`. -/
noncomputable def sectionsLeibnizDerivation
    (δ : ∀ X : Cᵒᵖ, A.obj.obj X → N.val.obj X)
    (hadd : ∀ (X : Cᵒᵖ) (x y : A.obj.obj X), δ X (x + y) = δ X x + δ X y)
    (hmul : ∀ (X : Cᵒᵖ) (x y : A.obj.obj X),
      δ X (x * y) = (φ.hom.app X).hom x • δ X y + (φ.hom.app X).hom y • δ X x)
    (hbase : ∀ (X : Cᵒᵖ) (r : R.obj.obj X), δ X ((a.hom.app X).hom r) = 0)
    (hnat : ∀ (X Y : Cᵒᵖ) (f : X ⟶ Y) (x : A.obj.obj X),
      δ Y (A.obj.map f x) = N.val.map f (δ X x)) :
    ((_root_.SheafOfModules.pushforward
      (underlyingRingHomForPullback J A B φ)).obj N).val.Derivation' a.hom where
  d {X} := AddMonoidHom.mk' (δ X) (hadd X)
  d_mul x y := hmul _ x y
  d_map f x := hnat _ _ f x
  d_app r := hbase _ r

/-- **Maps out of the middle term `B ⊗[A] Ω[A/R]` of the conormal sequence.**  A family of maps
on the sections of `A` which is additive, satisfies the Leibniz rule over `φ`, kills the
sections of `R` and commutes with the restriction maps classifies a morphism of sheaves of
`B`-modules out of the middle term.

This is the sheaf-level counterpart of `Stacks.NaiveCotangent.cotangentSpaceDesc`.  Together
with `tensorDifferentialsDesc_unique` it says that a derivation out of `B ⊗[A] Ω[A/R]` is
determined by, and constructible from, its values on the sections of `A`.

`@[no_expose]`: a public definition whose body is exposed may not mention a `private`
declaration, and the universal property this is read off is private plumbing.  A consumer needs
only `tensorDifferentialsDesc_tensorDifferential` and `tensorDifferentialsDesc_unique`, neither
of which requires the body. -/
@[no_expose]
noncomputable def tensorDifferentialsDesc
    (δ : ∀ X : Cᵒᵖ, A.obj.obj X → N.val.obj X)
    (hadd : ∀ (X : Cᵒᵖ) (x y : A.obj.obj X), δ X (x + y) = δ X x + δ X y)
    (hmul : ∀ (X : Cᵒᵖ) (x y : A.obj.obj X),
      δ X (x * y) = (φ.hom.app X).hom x • δ X y + (φ.hom.app X).hom y • δ X x)
    (hbase : ∀ (X : Cᵒᵖ) (r : R.obj.obj X), δ X ((a.hom.app X).hom r) = 0)
    (hnat : ∀ (X Y : Cᵒᵖ) (f : X ⟶ Y) (x : A.obj.obj X),
      δ Y (A.obj.map f x) = N.val.map f (δ X x)) :
    tensorDifferentialsSheaf.{v, u, w, z} J R A B a φ ⟶ N :=
  (tensorDifferentialsHomEquiv.{v, u, w, z} J R A B a φ N).symm
    (sectionsLeibnizDerivation.{v, u, w, z} J R A B a φ N δ hadd hmul hbase hnat)

/-- **The classifying morphism takes the prescribed value on each local section `1 ⊗ d x`.** -/
theorem tensorDifferentialsDesc_tensorDifferential
    (δ : ∀ X : Cᵒᵖ, A.obj.obj X → N.val.obj X)
    (hadd : ∀ (X : Cᵒᵖ) (x y : A.obj.obj X), δ X (x + y) = δ X x + δ X y)
    (hmul : ∀ (X : Cᵒᵖ) (x y : A.obj.obj X),
      δ X (x * y) = (φ.hom.app X).hom x • δ X y + (φ.hom.app X).hom y • δ X x)
    (hbase : ∀ (X : Cᵒᵖ) (r : R.obj.obj X), δ X ((a.hom.app X).hom r) = 0)
    (hnat : ∀ (X Y : Cᵒᵖ) (f : X ⟶ Y) (x : A.obj.obj X),
      δ Y (A.obj.map f x) = N.val.map f (δ X x))
    (X : Cᵒᵖ) (x : A.obj.obj X) :
    (tensorDifferentialsDesc.{v, u, w, z} J R A B a φ N δ hadd hmul hbase hnat).val.app X
        (tensorDifferential.{v, u, w, z} J R A B a φ X x) = δ X x := by
  refine Eq.trans (tensorDifferentialsHomEquiv_d.{v, u, w, z} J R A B a φ N
    (tensorDifferentialsDesc.{v, u, w, z} J R A B a φ N δ hadd hmul hbase hnat) X x).symm ?_
  exact congrArg (fun D : ((_root_.SheafOfModules.pushforward
      (underlyingRingHomForPullback J A B φ)).obj N).val.Derivation' a.hom ↦ D.d (X := X) x)
    ((tensorDifferentialsHomEquiv.{v, u, w, z} J R A B a φ N).apply_symm_apply
      (sectionsLeibnizDerivation.{v, u, w, z} J R A B a φ N δ hadd hmul hbase hnat))

/-- **The descent is the only morphism with the prescribed values.**  A morphism out of the
middle term agreeing with `δ` on every local section `1 ⊗ d x` is `tensorDifferentialsDesc`. -/
theorem tensorDifferentialsDesc_unique
    (δ : ∀ X : Cᵒᵖ, A.obj.obj X → N.val.obj X)
    (hadd : ∀ (X : Cᵒᵖ) (x y : A.obj.obj X), δ X (x + y) = δ X x + δ X y)
    (hmul : ∀ (X : Cᵒᵖ) (x y : A.obj.obj X),
      δ X (x * y) = (φ.hom.app X).hom x • δ X y + (φ.hom.app X).hom y • δ X x)
    (hbase : ∀ (X : Cᵒᵖ) (r : R.obj.obj X), δ X ((a.hom.app X).hom r) = 0)
    (hnat : ∀ (X Y : Cᵒᵖ) (f : X ⟶ Y) (x : A.obj.obj X),
      δ Y (A.obj.map f x) = N.val.map f (δ X x))
    (g : tensorDifferentialsSheaf.{v, u, w, z} J R A B a φ ⟶ N)
    (hg : ∀ (X : Cᵒᵖ) (x : A.obj.obj X),
      g.val.app X (tensorDifferential.{v, u, w, z} J R A B a φ X x) = δ X x) :
    g = tensorDifferentialsDesc.{v, u, w, z} J R A B a φ N δ hadd hmul hbase hnat :=
  tensorSheaf_hom_ext.{v, u, w, z} J R A B a φ N fun X x ↦ (hg X x).trans
    (tensorDifferentialsDesc_tensorDifferential.{v, u, w, z} J R A B a φ N
      δ hadd hmul hbase hnat X x).symm

/-- **The descent, read on the conormal class of a local section of the kernel.**  The
left-hand map of the conormal sequence followed by the descent of `δ` sends the conormal class
of `g` to `δ g`, the left-hand map sending it to `1 ⊗ d g`. -/
theorem tensorDifferentialsDesc_conormalClass
    (δ : ∀ X : Cᵒᵖ, A.obj.obj X → N.val.obj X)
    (hadd : ∀ (X : Cᵒᵖ) (x y : A.obj.obj X), δ X (x + y) = δ X x + δ X y)
    (hmul : ∀ (X : Cᵒᵖ) (x y : A.obj.obj X),
      δ X (x * y) = (φ.hom.app X).hom x • δ X y + (φ.hom.app X).hom y • δ X x)
    (hbase : ∀ (X : Cᵒᵖ) (r : R.obj.obj X), δ X ((a.hom.app X).hom r) = 0)
    (hnat : ∀ (X Y : Cᵒᵖ) (f : X ⟶ Y) (x : A.obj.obj X),
      δ Y (A.obj.map f x) = N.val.map f (δ X x))
    (X : Cᵒᵖ) (x : kernelIdeal φ.hom X) :
    (tensorDifferentialsDesc.{v, u, w, z} J R A B a φ N δ hadd hmul hbase hnat).val.app X
        ((conormalSequence.{v, u, w, z} J R A B a φ).f.val.app X
          (conormalClass.{v, u, w, z} J R A B a φ X x)) = δ X x.1 :=
  (congrArg (fun t ↦ (tensorDifferentialsDesc.{v, u, w, z} J R A B a φ N
      δ hadd hmul hbase hnat).val.app X t)
    (conormalSequence_f_class.{v, u, w, z} J R A B a φ X x)).trans
    (tensorDifferentialsDesc_tensorDifferential.{v, u, w, z} J R A B a φ N
      δ hadd hmul hbase hnat X x.1)

/-- **A morphism out of the conormal sheaf induced by a derivation factors through the degree
`0` term.**  If `ξ` sends the conormal class of every local section `g` of the kernel to `δ g`,
then `ξ` is the left-hand map of the conormal sequence followed by the descent of `δ`.

This is the factorisation `ξ = d ≫ θ` that makes such a class vanish in `Ext¹`; see
`AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm.conormalExtClass_eq_zero_iff`. -/
theorem conormalSequence_f_comp_tensorDifferentialsDesc
    (δ : ∀ X : Cᵒᵖ, A.obj.obj X → N.val.obj X)
    (hadd : ∀ (X : Cᵒᵖ) (x y : A.obj.obj X), δ X (x + y) = δ X x + δ X y)
    (hmul : ∀ (X : Cᵒᵖ) (x y : A.obj.obj X),
      δ X (x * y) = (φ.hom.app X).hom x • δ X y + (φ.hom.app X).hom y • δ X x)
    (hbase : ∀ (X : Cᵒᵖ) (r : R.obj.obj X), δ X ((a.hom.app X).hom r) = 0)
    (hnat : ∀ (X Y : Cᵒᵖ) (f : X ⟶ Y) (x : A.obj.obj X),
      δ Y (A.obj.map f x) = N.val.map f (δ X x))
    (ξ : (conormalSequence.{v, u, w, z} J R A B a φ).X₁ ⟶ N)
    (hξ : ∀ (X : Cᵒᵖ) (x : kernelIdeal φ.hom X),
      ξ.val.app X (conormalClass.{v, u, w, z} J R A B a φ X x) = δ X x.1) :
    (conormalSequence.{v, u, w, z} J R A B a φ).f ≫
        tensorDifferentialsDesc.{v, u, w, z} J R A B a φ N δ hadd hmul hbase hnat = ξ := by
  refine sheafify_hom_ext.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) N (fun X y ↦ ?_)
  obtain ⟨x, rfl⟩ := (kernelIdeal φ.hom X).toCotangent_surjective y
  exact (tensorDifferentialsDesc_conormalClass.{v, u, w, z} J R A B a φ N
    δ hadd hmul hbase hnat X x).trans (hξ X x).symm

end Sections

/-! ### The cokernels of the two conormal maps of a change of presentation -/

/-- The image-presheaf model of `Ω[B/R]` agrees with the sheaf of relative differentials of
any morphism `R ⟶ B` through which the presentation factors, carrying the differential of a
local section of the image presheaf to the universal differential of its image in `B`. -/
theorem exists_iso_moduleOfDifferentialsOfSite (c : R ⟶ B) (hc : a ≫ φ = c) :
    ∃ e : (conormalSequence.{v, u, w, z} J R A B a φ).X₃ ≅
        moduleOfDifferentialsOfSite.{v, u, w, z} R B c,
      ∀ (X : Cᵒᵖ) (x : A.obj.obj X),
        e.hom.val.app X
            (quotientDifferential.{v, u, w, z} J R A B a φ X (Ideal.Quotient.mk _ x)) =
          (universalDerivationOfSite.{v, u, w, z} R B c).d (φ.hom.app X x) := by
  subst hc
  exact exists_imageDifferentialsIso.{v, u, w, z} J R A B a φ

section CokernelChangeOfPresentation

variable (A₁ A₂ : Sheaf J CommRingCat.{w}) (a₁ : R ⟶ A₁) (a₂ : R ⟶ A₂)
  (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B) (ψ : A₁ ⟶ A₂)
  (hψ : ψ ≫ φ₂ = φ₁) (ha : a₁ ≫ ψ = a₂)
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]

/-- The right-hand maps of the conormal sequences of two presentations become equal once the
two right-hand terms are identified with `Ω[B/R]`: both carry the local section `1 ⊗ d f` to
the universal differential of the image of `f` in `B`, and the two images agree because
`ψ ≫ φ₂ = φ₁`. -/
theorem tensorSheafMapOfFac_comp_g_comp (c : R ⟶ B)
    (e₁ : (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).X₃ ⟶
      moduleOfDifferentialsOfSite.{v, u, w, z} R B c)
    (he₁ : ∀ (X : Cᵒᵖ) (x : A₁.obj.obj X),
      e₁.val.app X
          (quotientDifferential.{v, u, w, z} J R A₁ B a₁ φ₁ X (Ideal.Quotient.mk _ x)) =
        (universalDerivationOfSite.{v, u, w, z} R B c).d (φ₁.hom.app X x))
    (e₂ : (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).X₃ ⟶
      moduleOfDifferentialsOfSite.{v, u, w, z} R B c)
    (he₂ : ∀ (X : Cᵒᵖ) (x : A₂.obj.obj X),
      e₂.val.app X
          (quotientDifferential.{v, u, w, z} J R A₂ B a₂ φ₂ X (Ideal.Quotient.mk _ x)) =
        (universalDerivationOfSite.{v, u, w, z} R B c).d (φ₂.hom.app X x)) :
    tensorSheafMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha ≫
        (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).g ≫ e₂ =
      (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).g ≫ e₁ := by
  refine tensorSheaf_hom_ext.{v, u, w, z} J R A₁ B a₁ φ₁ _ (fun X x ↦ ?_)
  have happ : ψ.hom.app X ≫ φ₂.hom.app X = φ₁.hom.app X :=
    congrArg (fun t : A₁.obj ⟶ B.obj ↦ t.app X) (hom_of_comp_eq hψ)
  have hx : φ₂.hom.app X (ψ.hom.app X x) = φ₁.hom.app X x :=
    (CommRingCat.comp_apply (ψ.hom.app X) (φ₂.hom.app X) x).symm.trans
      (ConcreteCategory.congr_hom happ x)
  have hlhs : (tensorSheafMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha ≫
          (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).g ≫ e₂).val.app X
            (tensorDifferential.{v, u, w, z} J R A₁ B a₁ φ₁ X x) =
        (universalDerivationOfSite.{v, u, w, z} R B c).d (φ₁.hom.app X x) := by
    refine Eq.trans (congrArg (fun y ↦ e₂.val.app X
      ((conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).g.val.app X y))
      (tensorSheafMapOfFac_tensorDifferential.{v, u, w, z}
        J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha X x)) ?_
    refine Eq.trans (congrArg (e₂.val.app X)
      (conormalSequence_g_differential.{v, u, w, z} J R A₂ B a₂ φ₂ X (ψ.hom.app X x))) ?_
    exact (he₂ X (ψ.hom.app X x)).trans
      (congrArg
        (fun t : B.obj.obj X ↦ (universalDerivationOfSite.{v, u, w, z} R B c).d t) hx)
  have hrhs : ((conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).g ≫ e₁).val.app X
          (tensorDifferential.{v, u, w, z} J R A₁ B a₁ φ₁ X x) =
        (universalDerivationOfSite.{v, u, w, z} R B c).d (φ₁.hom.app X x) :=
    (congrArg (e₁.val.app X)
      (conormalSequence_g_differential.{v, u, w, z} J R A₁ B a₁ φ₁ X x)).trans (he₁ X x)
  exact hlhs.trans hrhs.symm

/-- The map induced by a change of presentation on the cokernels of the two conormal maps is
an isomorphism: both cokernels are `Ω[B/R]`, and the induced map is the identity of
`Ω[B/R]`. -/
theorem isIso_cokernel_map_conormalSequence_f
    [HasSheafify J AddCommGrpCat.{max w u v z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}] :
    IsIso (Limits.cokernel.map
      (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f
      (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f
      (conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ)
      (tensorSheafMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha)
      (conormalSequence_f_naturality.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha)) := by
  have hc₂ : a₂ ≫ φ₂ = a₁ ≫ φ₁ := by rw [← ha, Category.assoc, hψ]
  obtain ⟨e₁, he₁⟩ := exists_imageDifferentialsIso.{v, u, w, z} J R A₁ B a₁ φ₁
  obtain ⟨e₂, he₂⟩ := exists_iso_moduleOfDifferentialsOfSite.{v, u, w, z} J R A₂ B a₂ φ₂
    (a₁ ≫ φ₁) hc₂
  exact isIso_cokernel_map_of_g_comp_eq
    (conormalSequence_exact.{v, u, w, z} J R A₁ B a₁ φ₁)
    (conormalSequence_exact.{v, u, w, z} J R A₂ B a₂ φ₂) e₁ e₂ _ _ _
    (tensorSheafMapOfFac_comp_g_comp.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha
      (a₁ ≫ φ₁) e₁.hom he₁ e₂.hom he₂)

end CokernelChangeOfPresentation

end Stacks.Sites.Conormal

end
