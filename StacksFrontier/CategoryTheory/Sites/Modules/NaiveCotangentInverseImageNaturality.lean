module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalInverseImage
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentInverseImage

/-!
# The inverse image of the degree-zero term of the naive cotangent complex

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi and `a : A ⟶ B` a homomorphism of sheaves of
commutative rings on `D`. The universal property
`Stacks.SheafOfModules.naiveCotangentZeroDerivationEquiv` of the degree-`0` term
`B ⊗_{A[B]} Ω_{A[B]/A}` of the naive cotangent complex is natural in the coefficient module:
postcomposing a morphism out of that term corresponds to postcomposing the `A`-derivation of
`A[B]` it represents. Each of the six bijections composing the universal property of the inverse
image of that term is natural in the same sense, so the bijection of Stacks 08TZ between the
morphisms out of `f⁻¹(B ⊗_{A[B]} Ω_{A[B]/A})` and the morphisms out of the degree-`0` term for
`f⁻¹a` commutes with postcomposition, and the Yoneda argument turns it into an isomorphism of
the two degree-`0` terms.

## Main results

* `Stacks.SheafOfModules.naiveCotangentZeroDerivationEquiv_naturality`: the universal property
  of the degree-`0` term is natural in the coefficient module.
* `Stacks.SheafOfModules.inverseImageNaiveCotangentZeroDerivationEquiv_naturality`: the
  universal property of the inverse image of the degree-`0` term is natural in the coefficient
  module.
* `Stacks.SheafOfModules.inverseImageNaiveCotangentZeroHomEquiv_naturality`: the bijection of
  Stacks 08TZ on the degree-`0` terms commutes with postcomposition.
* `Stacks.SheafOfModules.inverseImageNaiveCotangentZeroIso`: the inverse image of the degree-`0`
  term is the degree-`0` term of the inverse image.

## Implementation notes

Every statement here is phrased at the spelling of the library lemma it instantiates, and every
proof applies library lemmas whose implicit arguments are determined by unification against the
goal. Two spellings of one coefficient module meet in the universal property of the degree-`0`
term: the extension/restriction of scalars adjunction produces the direct image of a sheaf of
modules along the identity functor, while the statement of the universal property reads it as a
restriction of scalars. The two agree by reflexivity, but the check is expensive, so it is made
exactly once, in `Stacks.SheafOfModules.naiveCotangentZeroDerivationEquiv_naturality`, whose
three constituent steps are composed beforehand in
`Stacks.SheafOfModules.zeroDerivationStep_comp_naturality` at the first of the two spellings.
For the same reason the chains below are broken into one declaration per step and composed by
rewriting, rather than assembled as a single term.

The third step compares the restriction of scalars of a direct image with the direct image of a
restriction of scalars. Its naturality is the naturality of that comparison as a natural
transformation, and crossing between the comparison at a single sheaf of modules and the
component of the natural transformation is the one identification the kernel cannot be asked to
make inside a larger statement: it is isolated in
`Stacks.SheafOfModules.directImageModulesRestrictScalarsIso_hom_val_naturality`, and the step
is reduced to a postcomposition once and for all in
`Stacks.SheafOfModules.inverseImageZeroStep₃_apply`.

The degree `-1` term, the isomorphism of the two conormal sheaves, is
`Stacks.Sheaves.RingedToposModules.inverseImageConormalIso`; its instantiation at the canonical
polynomial presentation and the resulting isomorphism of two-term complexes are not proved
here.

## References

* [Stacks Project, Tag 08TZ](https://stacks.math.columbia.edu/tag/08TZ)
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW), the naive cotangent
  complex.
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), the corepresentability
  of relative derivations.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.SheafOfModules

section NaiveCotangentZero

universe uu vv ww

open CategoryTheory AlgebraicGeometry.SheafOfModules Stacks.Sites.FreeAlgebra

variable {C : Type uu} [Category.{vv} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{max uu vv ww}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max uu vv ww} RingCat.{max uu vv ww})]
  (A B : Sheaf J CommRingCat.{max uu vv ww}) (a : A ⟶ B)

/-- The three steps of the universal property of the degree-`0` term of the naive cotangent
complex, composed, are natural in the coefficient module; the coefficients of the resulting
derivation are read as the direct image along the identity functor. -/
lemma zeroDerivationStep_comp_naturality
    {N N' : _root_.SheafOfModules.{max uu vv ww} (Stacks.SheafOfModules.Tensor.ringSheaf B)}
    (x : (canonicalConormalSequence.{vv, uu, max uu vv ww, max uu vv ww} J A B a).X₂ ⟶ N)
    (g : N ⟶ N') :
    zeroDerivationStep₃ J A B a N' (zeroDerivationStep₂ J A B a N'
        (zeroDerivationStep₁ J A B a N' (x ≫ g))) =
      (zeroDerivationStep₃ J A B a N
          (zeroDerivationStep₂ J A B a N (zeroDerivationStep₁ J A B a N x))).postcomp
        ((_root_.SheafOfModules.pushforward
          (Stacks.Sites.Conormal.underlyingRingHomForPullback J
            (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
            (canonicalPresentation J A B a))).map g).val :=
  (congrArg (fun z ↦ zeroDerivationStep₃ J A B a N' (zeroDerivationStep₂ J A B a N' z))
      (Category.assoc _ x g).symm).trans
    ((congrArg (zeroDerivationStep₃ J A B a N')
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction
          (Stacks.Sites.Conormal.underlyingRingHomForPullback J
            (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
            (canonicalPresentation J A B a))).homEquiv_naturality_right _ g)).trans
      ((derivationsFunctor.{max uu vv ww} A (freeAlgebraSheaf J A (underlyingPresheaf J B))
        (freeAlgebraSheafCoefficientMap J A
          (underlyingPresheaf J B))).corepresentableBy.homEquiv_comp _ _))

/-- **The universal property of the degree-`0` term of the naive cotangent complex is natural in
the coefficient module.** A morphism out of `B ⊗_{A[B]} Ω_{A[B]/A}` followed by a morphism of
sheaves of `B`-modules represents the `A`-derivation of `A[B]` represented by the morphism,
postcomposed with that morphism of modules. -/
lemma naiveCotangentZeroDerivationEquiv_naturality
    {N N' : _root_.SheafOfModules.{max uu vv ww} (Stacks.SheafOfModules.Tensor.ringSheaf B)}
    (x : (canonicalConormalSequence.{vv, uu, max uu vv ww, max uu vv ww} J A B a).X₂ ⟶ N)
    (g : N ⟶ N') :
    naiveCotangentZeroDerivationEquiv.{uu, vv, ww} J A B a N' (x ≫ g) =
      (naiveCotangentZeroDerivationEquiv.{uu, vv, ww} J A B a N x).postcomp
        ((_root_.SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{vv, uu, max uu vv ww} J).map
            (canonicalPresentation J A B a))).map g).val :=
  zeroDerivationStep_comp_naturality J A B a x g

end NaiveCotangentZero

section DerivationPostcomp

universe v₀ u₀ v₂ u₂

variable {D₀ : Type u₂} [Category.{v₂} D₀] {S R : D₀ᵒᵖ ⥤ CommRingCat.{u₀}}
  {M N P : PresheafOfModules.{v₀} (R ⋙ forget₂ CommRingCat.{u₀} RingCat.{u₀})} {φ : S ⟶ R}

/-- Postcomposing a derivation twice is postcomposing by the composition. -/
private lemma derivation_postcomp_postcomp (DD : PresheafOfModulesOfCommRing.Derivation' M φ)
    (α : M ⟶ N) (β : N ⟶ P) :
    (DD.postcomp α).postcomp β = DD.postcomp (α ≫ β) := rfl

end DerivationPostcomp

section InverseImageNaiveCotangentZero

universe u v w u' v' w'

open CategoryTheory AlgebraicGeometry.SheafOfModules Stacks.Sites.FreeAlgebra
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.ToposPushforward

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J CommRingCat.{max u v w}] [HasWeakSheafify K CommRingCat.{max u' v' w'}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})]
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
  {A B : Sheaf K CommRingCat.{max u' v' w'}} (a : A ⟶ B)

/-- The `A`-derivation of `A[B]` with values in the direct image of `M`, attached to a morphism
from the inverse image of the degree-`0` term of the naive cotangent complex of `a` to a sheaf
of `f⁻¹B`-modules `M`. -/
noncomputable def pushforwardZeroDerivation
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (h : (inverseImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M) :
    PresheafOfModulesOfCommRing.Derivation' (((_root_.SheafOfModules.restrictScalars
        ((Stacks.forgetCommRingSheaf.{v', u', max u' v' w'} K).map
          (canonicalPresentation K A B a))).obj
          ((directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
            M))).val
      (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)).hom :=
  inverseImageZeroStep₂ J K f a M (inverseImageZeroStep₁ J K f a M h)

omit [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- The hom-set bijection of the inverse image and the direct image of sheaves of modules is
natural in the target: the derivation attached to a postcomposed morphism is the one attached to
the direct image of that postcomposition. -/
lemma pushforwardZeroDerivation_comp
    {M M' : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))}
    (h : (inverseImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M)
    (g : M ⟶ M') :
    pushforwardZeroDerivation J K f a M' (h ≫ g) =
      inverseImageZeroStep₂ J K f a M' (inverseImageZeroStep₁ J K f a M h ≫
        (directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).map g) :=
  congrArg (inverseImageZeroStep₂ J K f a M')
    (toposModulesHomEquiv_naturality_right f
      (Tensor.ringSheaf.{u', v', max u' v' w'} B) _ h g)

omit [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- The universal property of the degree-`0` term on the target site is natural in the
coefficient module, here in the direct image of a morphism of sheaves of `f⁻¹B`-modules. -/
lemma inverseImageZeroStep₂_naturality
    {M M' : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))}
    (h : (inverseImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M)
    (g : M ⟶ M') :
    inverseImageZeroStep₂ J K f a M' (inverseImageZeroStep₁ J K f a M h ≫
        (directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).map g) =
      (pushforwardZeroDerivation J K f a M h).postcomp
        ((_root_.SheafOfModules.restrictScalars
            ((Stacks.forgetCommRingSheaf.{v', u', max u' v' w'} K).map
              (canonicalPresentation K A B a))).map
          ((directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).map g)).val :=
  naiveCotangentZeroDerivationEquiv_naturality K A B a _ _

omit [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- **The `A`-derivation attached to a morphism out of the inverse image of the degree-`0` term
is natural in the coefficient module.** This is the composition of the first two of the six
bijections composing the universal property of that inverse image. -/
lemma pushforwardZeroDerivation_naturality
    {M M' : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))}
    (h : (inverseImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M)
    (g : M ⟶ M') :
    pushforwardZeroDerivation J K f a M' (h ≫ g) =
      (pushforwardZeroDerivation J K f a M h).postcomp
        ((_root_.SheafOfModules.restrictScalars
            ((Stacks.forgetCommRingSheaf.{v', u', max u' v' w'} K).map
              (canonicalPresentation K A B a))).map
          ((directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).map g)).val := by
  rw [pushforwardZeroDerivation_comp, inverseImageZeroStep₂_naturality]

omit [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- The comparison of the restriction of scalars of a direct image with the direct image of a
restriction of scalars is natural in the sheaf of modules, read on underlying presheaves of
modules. -/
lemma directImageModulesRestrictScalarsIso_hom_val_naturality
    {M M' : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))}
    (g : M ⟶ M') :
    ((_root_.SheafOfModules.restrictScalars
            ((Stacks.forgetCommRingSheaf.{v', u', max u' v' w'} K).map
              (canonicalPresentation K A B a))).map
          ((directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).map g)).val ≫
        (directImageModulesRestrictScalarsIso f
          (underlyingRingHomOfSite (canonicalPresentation K A B a)) M').hom.val =
      (directImageModulesRestrictScalarsIso f
            (underlyingRingHomOfSite (canonicalPresentation K A B a)) M).hom.val ≫
        ((directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'}
            (freeAlgebraSheaf K A (underlyingPresheaf K B)))).map
          ((_root_.SheafOfModules.restrictScalars (inverseImageRingMap f
            (underlyingRingHomOfSite (canonicalPresentation K A B a)))).map g)).val :=
  congrArg _root_.SheafOfModules.Hom.val
    ((directImageModulesCompRestrictScalarsIso f
      (underlyingRingHomOfSite (canonicalPresentation K A B a))).hom.naturality g)

omit [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- The third of the six bijections composing the universal property of the inverse image of the
degree-`0` term is postcomposition by the comparison of the restriction of scalars of a direct
image with the direct image of a restriction of scalars. -/
lemma inverseImageZeroStep₃_apply
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (DD : PresheafOfModulesOfCommRing.Derivation'
        (((_root_.SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v', u', max u' v' w'} K).map
            (canonicalPresentation K A B a))).obj
          ((directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
            M))).val
        (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)).hom) :
    inverseImageZeroStep₃ J K f a M DD =
      DD.postcomp (directImageModulesRestrictScalarsIso f
        (underlyingRingHomOfSite (canonicalPresentation K A B a)) M).hom.val :=
  rfl

omit [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- The third of the six bijections composing the universal property of the inverse image of the
degree-`0` term is natural in the coefficient module. -/
lemma inverseImageZeroStep₃_naturality
    {M M' : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))}
    (g : M ⟶ M')
    (DD : PresheafOfModulesOfCommRing.Derivation'
        (((_root_.SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v', u', max u' v' w'} K).map
            (canonicalPresentation K A B a))).obj
          ((directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
            M))).val
        (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)).hom) :
    inverseImageZeroStep₃ J K f a M' (DD.postcomp
        ((_root_.SheafOfModules.restrictScalars
            ((Stacks.forgetCommRingSheaf.{v', u', max u' v' w'} K).map
              (canonicalPresentation K A B a))).map
          ((directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).map g)).val) =
      (inverseImageZeroStep₃ J K f a M DD).postcomp
        ((directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'}
            (freeAlgebraSheaf K A (underlyingPresheaf K B)))).map
          ((_root_.SheafOfModules.restrictScalars (inverseImageRingMap f
            (underlyingRingHomOfSite (canonicalPresentation K A B a)))).map g)).val := by
  rw [inverseImageZeroStep₃_apply, inverseImageZeroStep₃_apply]
  exact (derivation_postcomp_postcomp _ _ _).trans
    ((congrArg (fun m ↦ PresheafOfModulesOfCommRing.Derivation.postcomp DD
          (_root_.SheafOfModules.Hom.val m))
        ((directImageModulesCompRestrictScalarsIso f
          (underlyingRingHomOfSite (canonicalPresentation K A B a))).hom.naturality g)).trans
      (derivation_postcomp_postcomp _ _ _).symm)

omit [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- The fourth of the six bijections composing the universal property of the inverse image of
the degree-`0` term, the transposition of derivations along `f⁻¹ ⊣ f_*`, is natural in the
coefficient module. -/
lemma inverseImageZeroStep₄_naturality
    {M M' : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))}
    (g : M ⟶ M')
    (DD : PresheafOfModulesOfCommRing.Derivation'
        (((directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'}
            (freeAlgebraSheaf K A (underlyingPresheaf K B)))).obj
          ((_root_.SheafOfModules.restrictScalars (inverseImageRingMap f
            (underlyingRingHomOfSite (canonicalPresentation K A B a)))).obj M)).val)
        (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B)).hom) :
    inverseImageZeroStep₄ J K f a M' (DD.postcomp
        ((directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'}
            (freeAlgebraSheaf K A (underlyingPresheaf K B)))).map
          ((_root_.SheafOfModules.restrictScalars (inverseImageRingMap f
            (underlyingRingHomOfSite (canonicalPresentation K A B a)))).map g)).val) =
      (inverseImageZeroStep₄ J K f a M DD).postcomp
        ((_root_.SheafOfModules.restrictScalars (inverseImageRingMap f
          (underlyingRingHomOfSite (canonicalPresentation K A B a)))).map g).val :=
  (inverseImageDerivationEquiv_symm_postcomp f
    (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))
    ((_root_.SheafOfModules.restrictScalars (inverseImageRingMap f
      (underlyingRingHomOfSite (canonicalPresentation K A B a)))).map g) DD).symm

omit [HasWeakSheafify J CommRingCat.{max u v w}] in
/-- The fifth of the six bijections composing the universal property of the inverse image of the
degree-`0` term, the transport along the equality of the two restriction morphisms, is natural
in the coefficient module. -/
lemma inverseImageZeroStep₅_naturality
    {M M' : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))}
    (g : M ⟶ M')
    (DD : PresheafOfModulesOfCommRing.Derivation'
        (((show _root_.SheafOfModules.{max u v w} (Tensor.ringSheaf.{u, v, max u v w}
            (f.inverseImageRing.obj (freeAlgebraSheaf K A (underlyingPresheaf K B)))) from
          (_root_.SheafOfModules.restrictScalars (inverseImageRingMap f
            (underlyingRingHomOfSite (canonicalPresentation K A B a)))).obj M)).val)
        (f.inverseImageRing.map
          (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))).hom) :
    inverseImageZeroStep₅ J K f a M' (DD.postcomp
        ((_root_.SheafOfModules.restrictScalars (inverseImageRingMap f
          (underlyingRingHomOfSite (canonicalPresentation K A B a)))).map g).val) =
      (inverseImageZeroStep₅ J K f a M DD).postcomp
        ((_root_.SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v, u, max u v w} J).map
            (f.inverseImageRing.map (canonicalPresentation K A B a)))).map g).val :=
  restrictScalarsDerivationCongr_postcomp g
    (forgetCommRingSheaf_map_pullbackCommRingSheafMap J f.inverseImage
      (canonicalPresentation K A B a)).symm
    (f.inverseImageRing.map (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))) DD

omit [K.HasSheafCompose (forget₂ CommRingCat.{max u' v' w'} RingCat.{max u' v' w'})] in
/-- The sixth of the six bijections composing the universal property of the inverse image of the
degree-`0` term, the transport along the identification of the two free algebras, is natural in
the coefficient module. -/
lemma inverseImageZeroStep₆_naturality
    {M M' : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))}
    (g : M ⟶ M')
    (DD : PresheafOfModulesOfCommRing.Derivation'
        (((_root_.SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v, u, max u v w} J).map
            (f.inverseImageRing.map (canonicalPresentation K A B a)))).obj M).val)
        (f.inverseImageRing.map
          (freeAlgebraSheafCoefficientMap K A (underlyingPresheaf K B))).hom) :
    inverseImageZeroStep₆ J K f a M' (DD.postcomp
        ((_root_.SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v, u, max u v w} J).map
            (f.inverseImageRing.map (canonicalPresentation K A B a)))).map g).val) =
      (inverseImageZeroStep₆ J K f a M DD).postcomp
        ((_root_.SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v, u, max u v w} J).map
            (canonicalPresentation J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
              (f.inverseImageRing.map a)))).map g).val :=
  derivationRingEquiv_postcomp g (inverseImageFreeAlgebraIso f A B)
    (map_coefficientMap_comp_inverseImageFreeAlgebraHom f A B)
    (inverseImageFreeAlgebraHom_comp_canonicalPresentation f A B a) DD

omit [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- The first three of the six bijections composing the universal property of the inverse image
of the degree-`0` term, composed, are natural in the coefficient module. -/
lemma inverseImageZeroStep₃_comp_naturality
    {M M' : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))}
    (h : (inverseImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M)
    (g : M ⟶ M') :
    inverseImageZeroStep₃ J K f a M' (pushforwardZeroDerivation J K f a M' (h ≫ g)) =
      (inverseImageZeroStep₃ J K f a M (pushforwardZeroDerivation J K f a M h)).postcomp
        ((directImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'}
            (freeAlgebraSheaf K A (underlyingPresheaf K B)))).map
          ((_root_.SheafOfModules.restrictScalars (inverseImageRingMap f
            (underlyingRingHomOfSite (canonicalPresentation K A B a)))).map g)).val := by
  rw [pushforwardZeroDerivation_naturality, inverseImageZeroStep₃_naturality]

omit [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- The first four of the six bijections composing the universal property of the inverse image
of the degree-`0` term, composed, are natural in the coefficient module. -/
lemma inverseImageZeroStep₄_comp_naturality
    {M M' : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))}
    (h : (inverseImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M)
    (g : M ⟶ M') :
    inverseImageZeroStep₄ J K f a M' (inverseImageZeroStep₃ J K f a M'
        (pushforwardZeroDerivation J K f a M' (h ≫ g))) =
      (inverseImageZeroStep₄ J K f a M (inverseImageZeroStep₃ J K f a M
          (pushforwardZeroDerivation J K f a M h))).postcomp
        ((_root_.SheafOfModules.restrictScalars (inverseImageRingMap f
          (underlyingRingHomOfSite (canonicalPresentation K A B a)))).map g).val := by
  rw [inverseImageZeroStep₃_comp_naturality, inverseImageZeroStep₄_naturality]

omit [HasWeakSheafify J CommRingCat.{max u v w}] in
/-- The first five of the six bijections composing the universal property of the inverse image
of the degree-`0` term, composed, are natural in the coefficient module. -/
lemma inverseImageZeroStep₅_comp_naturality
    {M M' : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))}
    (h : (inverseImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M)
    (g : M ⟶ M') :
    inverseImageZeroStep₅ J K f a M' (inverseImageZeroStep₄ J K f a M'
        (inverseImageZeroStep₃ J K f a M'
          (pushforwardZeroDerivation J K f a M' (h ≫ g)))) =
      (inverseImageZeroStep₅ J K f a M (inverseImageZeroStep₄ J K f a M
          (inverseImageZeroStep₃ J K f a M
            (pushforwardZeroDerivation J K f a M h)))).postcomp
        ((_root_.SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v, u, max u v w} J).map
            (f.inverseImageRing.map (canonicalPresentation K A B a)))).map g).val := by
  rw [inverseImageZeroStep₄_comp_naturality, inverseImageZeroStep₅_naturality]

/-- All six bijections composing the universal property of the inverse image of the degree-`0`
term, composed, are natural in the coefficient module. -/
lemma inverseImageZeroStep₆_comp_naturality
    {M M' : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))}
    (h : (inverseImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M)
    (g : M ⟶ M') :
    inverseImageZeroStep₆ J K f a M' (inverseImageZeroStep₅ J K f a M'
        (inverseImageZeroStep₄ J K f a M' (inverseImageZeroStep₃ J K f a M'
          (pushforwardZeroDerivation J K f a M' (h ≫ g))))) =
      (inverseImageZeroStep₆ J K f a M (inverseImageZeroStep₅ J K f a M
          (inverseImageZeroStep₄ J K f a M (inverseImageZeroStep₃ J K f a M
            (pushforwardZeroDerivation J K f a M h))))).postcomp
        ((_root_.SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v, u, max u v w} J).map
            (canonicalPresentation J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
              (f.inverseImageRing.map a)))).map g).val := by
  rw [inverseImageZeroStep₅_comp_naturality, inverseImageZeroStep₆_naturality]

/-- The universal property of the inverse image of the degree-`0` term is the composition of its
six constituent bijections, the first two of which are `pushforwardZeroDerivation`. -/
lemma inverseImageNaiveCotangentZeroDerivationEquiv_apply
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (h : (inverseImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M) :
    inverseImageNaiveCotangentZeroDerivationEquiv J K f a M h =
      inverseImageZeroStep₆ J K f a M (inverseImageZeroStep₅ J K f a M
        (inverseImageZeroStep₄ J K f a M (inverseImageZeroStep₃ J K f a M
          (pushforwardZeroDerivation J K f a M h)))) :=
  rfl

/-- **The universal property of the inverse image of the degree-`0` term of the naive cotangent
complex is natural in the coefficient module.** A morphism out of `f⁻¹(B ⊗_{A[B]} Ω_{A[B]/A})`
followed by a morphism of sheaves of `f⁻¹B`-modules represents the `f⁻¹A`-derivation represented
by the morphism, postcomposed with that morphism of modules. -/
lemma inverseImageNaiveCotangentZeroDerivationEquiv_naturality
    {M M' : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))}
    (h : (inverseImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M)
    (g : M ⟶ M') :
    inverseImageNaiveCotangentZeroDerivationEquiv J K f a M' (h ≫ g) =
      (inverseImageNaiveCotangentZeroDerivationEquiv J K f a M h).postcomp
        ((_root_.SheafOfModules.restrictScalars
          ((Stacks.forgetCommRingSheaf.{v, u, max u v w} J).map
            (canonicalPresentation J (f.inverseImageRing.obj A) (f.inverseImageRing.obj B)
              (f.inverseImageRing.map a)))).map g).val := by
  rw [inverseImageNaiveCotangentZeroDerivationEquiv_apply,
    inverseImageNaiveCotangentZeroDerivationEquiv_apply,
    inverseImageZeroStep₆_comp_naturality]

/-- The bijection of Stacks 08TZ on morphisms out of the two degree-`0` terms is the universal
property of the inverse image followed by the inverse of the universal property of the
degree-`0` term of the inverse image. -/
lemma inverseImageNaiveCotangentZeroHomEquiv_apply
    (M : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B)))
    (h : (inverseImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M) :
    inverseImageNaiveCotangentZeroHomEquiv J K f a M h =
      (naiveCotangentZeroDerivationEquiv.{u, v, w} J (f.inverseImageRing.obj A)
          (f.inverseImageRing.obj B) (f.inverseImageRing.map a) M).symm
        (inverseImageNaiveCotangentZeroDerivationEquiv J K f a M h) :=
  rfl

/-- **The bijection of Stacks 08TZ on the degree-`0` terms is natural in the coefficient
module.** Transporting a morphism out of `f⁻¹(B ⊗_{A[B]} Ω_{A[B]/A})` and then postcomposing a
morphism of sheaves of `f⁻¹B`-modules is postcomposing that morphism and then transporting. -/
lemma inverseImageNaiveCotangentZeroHomEquiv_naturality
    {M M' : _root_.SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (f.inverseImageRing.obj B))}
    (h : (inverseImageModules f
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ⟶ M)
    (g : M ⟶ M') :
    inverseImageNaiveCotangentZeroHomEquiv J K f a M' (h ≫ g) =
      inverseImageNaiveCotangentZeroHomEquiv J K f a M h ≫ g := by
  rw [inverseImageNaiveCotangentZeroHomEquiv_apply,
    inverseImageNaiveCotangentZeroHomEquiv_apply, Equiv.symm_apply_eq,
    naiveCotangentZeroDerivationEquiv_naturality, Equiv.apply_symm_apply,
    inverseImageNaiveCotangentZeroDerivationEquiv_naturality]

/-- The bijection of Stacks 08TZ on the degree-`0` terms commutes with postcomposition, the
hypothesis of the Yoneda argument `isoOfNaturalHomEquiv`. -/
lemma naturalHomEquiv_inverseImageNaiveCotangentZeroHomEquiv :
    NaturalHomEquiv (inverseImageNaiveCotangentZeroHomEquiv J K f a) :=
  fun _ _ h g ↦ inverseImageNaiveCotangentZeroHomEquiv_naturality J K f a h g

/-- **The inverse image of the degree-`0` term of the naive cotangent complex is the degree-`0`
term of the naive cotangent complex of the inverse image**:
`f⁻¹(B ⊗_{A[B]} Ω_{A[B]/A}) ≅ f⁻¹B ⊗_{(f⁻¹A)[f⁻¹B]} Ω_{(f⁻¹A)[f⁻¹B]/f⁻¹A}`. -/
@[stacks 08TZ "the degree 0 term as an isomorphism, obtained from naturality of the \
corepresentability bijection by Yoneda. The degree -1 term is `inverseImageConormalIso` and \
the isomorphism of complexes assembled from the two is \
`Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso`"]
noncomputable def inverseImageNaiveCotangentZeroIso :
    (inverseImageModules f (Tensor.ringSheaf.{u', v', max u' v' w'} B)).obj
        (canonicalConormalSequence.{v', u', max u' v' w', max u' v' w'} K A B a).X₂ ≅
      (canonicalConormalSequence.{v, u, max u v w, max u v w} J (f.inverseImageRing.obj A)
        (f.inverseImageRing.obj B) (f.inverseImageRing.map a)).X₂ :=
  isoOfNaturalHomEquiv (inverseImageNaiveCotangentZeroHomEquiv J K f a)
    (naturalHomEquiv_inverseImageNaiveCotangentZeroHomEquiv J K f a)

end InverseImageNaiveCotangentZero

end Stacks.SheafOfModules

end
