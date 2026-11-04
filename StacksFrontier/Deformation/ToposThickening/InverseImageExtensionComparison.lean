module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.Deformation.RingedSpaceThickening.InverseImageExtensionComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The pushout and pullback extensions of Stacks 0GQ8, and the criterion comparing them

Let `f : (Sh(𝒞), 𝒪_𝒞) ⟶ (Sh(ℬ), 𝒪_ℬ)` and `g : (Sh(𝒟), 𝒪_𝒟) ⟶ (Sh(𝒞), 𝒪_𝒞)` be morphisms of
ringed topoi, let

* `0 ⟶ ℱ ⟶ 𝒪_{𝒞'} ⟶ 𝒪_𝒞 ⟶ 0` be an extension of `f⁻¹𝒪_ℬ`-algebras,
* `0 ⟶ 𝒢 ⟶ 𝒪_{𝒟'} ⟶ 𝒪_𝒟 ⟶ 0` an extension of `g⁻¹f⁻¹𝒪_ℬ`-algebras,

and let `c : g^*ℱ ⟶ 𝒢` be an `𝒪_𝒟`-linear map, as in **Stacks 0GQ7**.  The remark
**Stacks 0GQ8** builds two extensions of `g⁻¹𝒪_𝒞` by `𝒢` over `g⁻¹f⁻¹𝒪_ℬ` —

* `𝒪'₁`, the pushout of `g⁻¹𝒪_{𝒞'}` along `c : g⁻¹ℱ ⟶ 𝒢`, and
* `𝒪'₂ = 𝒪_{𝒟'} ×_{𝒪_𝒟} g⁻¹𝒪_𝒞`, the pullback of `𝒪_{𝒟'}` along `g^♯ : g⁻¹𝒪_𝒞 ⟶ 𝒪_𝒟` —

and proves, by a diagram chase, that a morphism `g' : (Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})` of
ringed topoi over `(Sh(ℬ), 𝒪_ℬ)` compatible with `g` and `c` exists if and only if `𝒪'₁` and
`𝒪'₂` are isomorphic as `g⁻¹f⁻¹𝒪_ℬ`-algebra extensions of `g⁻¹𝒪_𝒞` by `𝒢`.  This file carries
out both constructions for a genuine pair of morphisms of ringed topoi and proves that
criterion.

Everything the remark compares lives on `𝒟`, so the two constructions and the chase are the ones of
**Stacks 0GQ2**, available on an arbitrary site through
`Stacks.Deformation.InverseImageExtension.Data`.  What this file supplies is the ringed-topos input
and the dictionary turning it into that site-level datum: `Data.toData` produces `A' = g⁻¹𝒪_{𝒞'}`,
`A = g⁻¹𝒪_𝒞`, `S = g⁻¹f⁻¹𝒪_ℬ` as *actual* inverse images along `g` of sheaves on `𝒞`,
`π = g⁻¹`(reduction), `q = g^♯` as the inverse-image form of the structure map of `g`, `B' = 𝒪_{𝒟'}`
and `B = 𝒪_𝒟`.

## Main definitions

* `Deformation.ToposThickening.InverseImageExtension.Data`: the ringed-topos input of
  **Stacks 0GQ8** — the two extensions, the prescribed map `c`, and the two algebra structures
  over `f⁻¹𝒪_ℬ`.
* `Deformation.ToposThickening.InverseImageExtension.Data.toData`: the dictionary, the
  site-level datum of **Stacks 0GQ2** on `𝒟` built from it.
* `Deformation.ToposThickening.InverseImageExtension.Data.pushoutExtension` and
  `Data.pullbackExtension`: the extensions `𝒪'₁` and `𝒪'₂`.
* `Deformation.ToposThickening.InverseImageExtension.Data.CompatibleHom`: the morphism `g'`, in
  its comorphism form `g⁻¹𝒪_{𝒞'} ⟶ 𝒪_{𝒟'}`.
* `Deformation.ToposThickening.InverseImageExtension.Data.toRingedToposHom` and
  `Data.compatibleRingedToposHom`: the morphism of ringed topoi
  `(Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})` such a comorphism is, between the thickened ringed topoi
  `Data.thickenedSource` and `Data.thickenedTarget`.

## Main results

* `Deformation.ToposThickening.InverseImageExtension.isLocallySurjective_invImage_map`: the
  inverse image along a morphism of ringed topoi of a locally surjective morphism of sheaves of
  commutative rings is locally surjective.  This is what makes `g⁻¹𝒪_{𝒞'} ⟶ g⁻¹𝒪_𝒞` an
  extension, and it is proved here rather than assumed.
* `Deformation.ToposThickening.InverseImageExtension.Data.ringedToposHomEquiv`: a morphism of
  ringed topoi `(Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})` inducing `g` on the underlying topoi is the
  same datum as a comorphism `g⁻¹𝒪_{𝒞'} ⟶ 𝒪_{𝒟'}` of sheaves of commutative rings.
* `Deformation.ToposThickening.InverseImageExtension.Data.nonempty_compatibleHom_iff_isomorphic`:
  **the criterion of Stacks 0GQ8** — such a morphism `g'` over `(Sh(ℬ), 𝒪_ℬ)` compatible with
  `g` and `c` exists if and only if `𝒪'₁` and `𝒪'₂` are isomorphic as extensions of `g⁻¹𝒪_𝒞` by
  `𝒢` over `g⁻¹f⁻¹𝒪_ℬ`.

## Implementation notes

**What is proved here that the ringed-space twin assumes.**  For the twin
`Stacks.Deformation.InverseImageExtension.Data`, that `g⁻¹𝒪_{𝒞'}` *is* an extension of `g⁻¹𝒪_𝒞` by
`g⁻¹ℱ` is assumed.  Here both halves of that are proved.  The kernel half is not even an input: the
ideal of the front extension is taken to be the kernel ideal of `g⁻¹`(reduction), and its
identification with `g⁻¹ℱ` is the left exactness of `g⁻¹`, the
`MorphismOfTopoi.preservesFiniteLimits` field of `g`.  The surjectivity half is
`isLocallySurjective_invImage_map`: a locally surjective morphism of sheaves of commutative rings is
an epimorphism of the underlying sheaves of sets, `g⁻¹` is a left adjoint and so preserves
epimorphisms, and on a site with sheafification an epimorphism of sheaves of sets is again locally
surjective.  Consequently the statements below assume nothing beyond the `Data` and the instances of
the variable block.

**What remains a hypothesis.**  Exactly the two structural facts about `𝒢` that the twin
also assumes, `Data.inr_mul_inr` and `Data.smul_inr`, because the formalized back input is the
locally surjective `p : 𝒪_{𝒟'} ⟶ 𝒪_𝒟` with a realization `ι` of its kernel rather than a
thickening of ringed topoi; both are part of the source's standing assumption that `𝒢` is an
`𝒪_𝒟`-module which is the square-zero ideal of `𝒪_{𝒟'}`.  The module `𝒢` is carried over
`g⁻¹𝒪_{𝒞'}` rather than over `𝒪_𝒟`, again as in the twin, and `Data.smul_inr` is what ties the
two actions together through `g^♯ ∘ g⁻¹`(reduction).

**The morphism `g'`.**  A morphism of ringed topoi `(Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})` inducing
`g` on the underlying topoi is a map `𝒪_{𝒞'} ⟶ g_*𝒪_{𝒟'}`, equivalently — by
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`, which is `Data.ringedToposHomEquiv` —
a comorphism `g⁻¹𝒪_{𝒞'} ⟶ 𝒪_{𝒟'}`.  The criterion is stated for the comorphism form, which is
the form in which the three compatibilities of the source are expressible; that the comorphism
form really is a morphism of ringed topoi between the two thickenings is
`Data.compatibleRingedToposHom`, and `Data.compatibleRingedToposHom_base`,
`Data.compatibleRingedToposHom_comp_p` and `Data.compatibleRingedToposHom_kernel` are its three
compatibilities read back off it — lying over `(Sh(ℬ), 𝒪_ℬ)`, lying over `g`, and inducing `c`.

**Universes.**  Both `(Sh(𝒞), 𝒪_𝒞)` and `(Sh(𝒟), 𝒪_𝒟)` are
`AlgebraicGeometry.RingedTopos.{u, u, u}`, as in
`Deformation.ToposThickening.RingedToposExtensionProblem.classesEquivExt`: the site-level machinery
of **Stacks 0GQ2** is stated for a small site whose sheaves of commutative rings have sections in
the universe of the site, and it is applied here on the site of `𝒟` while the inverse images come
from the site of `𝒞`.  The base ringed topos `(Sh(ℬ), 𝒪_ℬ)` is unconstrained.

## References

* [Stacks Project, Tag 0GQ8](https://stacks.math.columbia.edu/tag/0GQ8)
* [Stacks Project, Tag 0GQ2](https://stacks.math.columbia.edu/tag/0GQ2), the ringed-space twin
  of this remark, whose two constructions and diagram chase are reused.
* [Stacks Project, Tag 0GQ7](https://stacks.math.columbia.edu/tag/0GQ7), the lemma this remark
  gives a direct argument for.
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC), the pushout.
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3), ringed topoi and their
  morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.Differentials (underlyingRingSheaf)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor pushforwardCommRingFunctor
  commRingImageAdjunction)
open Stacks.Sites.Conormal (kernelIdeal)
open Stacks.Sites.SqZeroExtension (AlgebraExtension)
open Stacks.Sites.SqZeroPullback (FibreInrData)
open Stacks.Sites.SqZeroPushout (PushoutData modules)

universe u v' u' w'

namespace Deformation.ToposThickening.InverseImageExtension

variable {Y X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [X.J.HasSheafCompose (forget CommRingCat.{u})]

/-- `f⁻¹𝒪_ℬ`, the sheaf of rings on `𝒞` over which the front extension is an extension of
algebras. -/
abbrev baseRing (f : RingedToposHom X B) : Sheaf X.J CommRingCat.{u} :=
  (inverseImageCommRingFunctor f.toToposHom).obj B.O

/-- `g⁻¹`, the inverse image of sheaves of commutative rings along a morphism of ringed
topoi. -/
abbrev invImage (g : RingedToposHom Y X) :
    Sheaf X.J CommRingCat.{u} ⥤ Sheaf Y.J CommRingCat.{u} :=
  inverseImageCommRingFunctor g.toToposHom

/-- **The inverse image of a locally surjective morphism of sheaves of commutative rings is
locally surjective.**  A locally surjective morphism is an epimorphism of the underlying sheaves
of sets, `g⁻¹` is a left adjoint and so preserves epimorphisms, and an epimorphism of sheaves of
sets on a site with sheafification is locally surjective. -/
theorem isLocallySurjective_invImage_map (g : RingedToposHom Y X)
    {A A' : Sheaf X.J CommRingCat.{u}} (π : A' ⟶ A)
    (hπ : Presheaf.IsLocallySurjective X.J π.hom) :
    Presheaf.IsLocallySurjective Y.J ((invImage g).map π).hom := by
  have hepi₀ : Epi ((sheafCompose X.J (forget CommRingCat.{u})).map π) :=
    (Sheaf.isLocallySurjective_iff_epi ((sheafCompose X.J (forget CommRingCat.{u})).map π)).1
      ((Presheaf.isLocallySurjective_iff_whisker_forget X.J π.hom).1 hπ)
  have hpres := Functor.preservesEpimorphisms_of_adjunction g.toToposHom.adj
  have key : (sheafCompose Y.J (forget CommRingCat.{u})).map ((invImage g).map π)
      = g.toToposHom.inverseImage.map ((sheafCompose X.J (forget CommRingCat.{u})).map π) :=
    Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap Y.J
      g.toToposHom.inverseImage π
  have hepi : Epi ((sheafCompose Y.J (forget CommRingCat.{u})).map ((invImage g).map π)) := by
    rw [key]
    exact hpres.preserves ((sheafCompose X.J (forget CommRingCat.{u})).map π)
  exact (Presheaf.isLocallySurjective_iff_whisker_forget Y.J ((invImage g).map π).hom).2
    ((Sheaf.isLocallySurjective_iff_epi _).2 hepi)

/-- **The ringed-topos input of Stacks 0GQ8**: an extension `0 ⟶ ℱ ⟶ 𝒪_{𝒞'} ⟶ 𝒪_𝒞 ⟶ 0` of
`f⁻¹𝒪_ℬ`-algebras, an extension `0 ⟶ 𝒢 ⟶ 𝒪_{𝒟'} ⟶ 𝒪_𝒟 ⟶ 0` of `g⁻¹f⁻¹𝒪_ℬ`-algebras, and the
prescribed map `c : g⁻¹ℱ ⟶ 𝒢`.  The ideal `ℱ` is the kernel of the reduction and so is not
separate data; the ideal `𝒢` is carried as a sheaf of modules together with an identification
`ι` of it with the kernel of the reduction `𝒪_{𝒟'} ⟶ 𝒪_𝒟`. -/
structure Data (f : RingedToposHom X B) (g : RingedToposHom Y X) where
  /-- The thickened structure sheaf `𝒪_{𝒞'}`. -/
  OC' : Sheaf X.J CommRingCat.{u}
  /-- The reduction `𝒪_{𝒞'} ⟶ 𝒪_𝒞`, whose kernel is the `𝒪_𝒞`-module `ℱ`. -/
  reduction : OC' ⟶ X.O
  /-- The reduction `𝒪_{𝒞'} ⟶ 𝒪_𝒞` is locally surjective. -/
  locallySurjective_reduction : Presheaf.IsLocallySurjective X.J reduction.hom
  /-- The `f⁻¹𝒪_ℬ`-algebra structure of `𝒪_{𝒞'}`. -/
  fromBase : baseRing f ⟶ OC'
  /-- The ideal `𝒢` of the back extension, read as a module over `g⁻¹𝒪_{𝒞'}`. -/
  G : SheafOfModules.{u} (underlyingRingSheaf ((invImage g).obj OC'))
  /-- The prescribed map `c : g⁻¹ℱ ⟶ 𝒢`, out of the kernel ideal of `g⁻¹`(reduction) and in the
  form the pushout of **Stacks 08UC** consumes. -/
  c : PushoutData ((invImage g).map reduction) G
  /-- The thickened structure sheaf `𝒪_{𝒟'}`. -/
  OD' : Sheaf Y.J CommRingCat.{u}
  /-- The reduction `𝒪_{𝒟'} ⟶ 𝒪_𝒟`. -/
  p : OD' ⟶ Y.O
  /-- The reduction `𝒪_{𝒟'} ⟶ 𝒪_𝒟` is locally surjective. -/
  locallySurjective_p : Presheaf.IsLocallySurjective Y.J p.hom
  /-- The identification of `𝒢` with the kernel of the reduction `𝒪_{𝒟'} ⟶ 𝒪_𝒟`. -/
  ι : FibreInrData p G.val.presheaf
  /-- The ideal `𝒢` of `𝒪_{𝒟'}` squares to zero. -/
  inr_mul_inr (U : Y.Cᵒᵖ) (n m : ↥((modules G).obj U)) : ι.app U n * ι.app U m = 0
  /-- The `g⁻¹𝒪_{𝒞'}`-module structure of `𝒢` is the restriction, along `g^♯ ∘ g⁻¹`(reduction),
  of the action of `𝒪_{𝒟'}` on its ideal `𝒢`. -/
  smul_inr (U : Y.Cᵒᵖ) (b : ↥(OD'.obj.obj U)) (a : ↥(((invImage g).obj OC').obj.obj U))
      (n : ↥((modules G).obj U))
      (hb : p.hom.app U b =
        g.fSharpInverseImage.hom.app U (((invImage g).map reduction).hom.app U a)) :
    b * ι.app U n = ι.app U (a • n)
  /-- The `g⁻¹f⁻¹𝒪_ℬ`-algebra structure of `𝒪_{𝒟'}`. -/
  fromBaseBack : (invImage g).obj (baseRing f) ⟶ OD'
  /-- Both extensions lie over `g⁻¹f⁻¹𝒪_ℬ`. -/
  base_comm : fromBaseBack ≫ p = (invImage g).map (fromBase ≫ reduction) ≫ g.fSharpInverseImage

namespace Data

variable {f : RingedToposHom X B} {g : RingedToposHom Y X} (d : Data f g)

/-- The surjection `g⁻¹𝒪_{𝒞'} ⟶ g⁻¹𝒪_𝒞`, the inverse image along `g` of the reduction.  Its
kernel ideal is `g⁻¹ℱ`. -/
abbrev invReduction : (invImage g).obj d.OC' ⟶ (invImage g).obj X.O :=
  (invImage g).map d.reduction

/-- The `g⁻¹f⁻¹𝒪_ℬ`-algebra structure of `g⁻¹𝒪_𝒞`, over which the two extensions of the remark
are compared. -/
abbrev invBase : (invImage g).obj (baseRing f) ⟶ (invImage g).obj X.O :=
  (invImage g).map d.fromBase ≫ d.invReduction

/-- **The dictionary of Stacks 0GQ8.**  The remark compares two extensions of sheaves of rings
on `𝒟`, so its content is the datum of **Stacks 0GQ2** on the site of `𝒟` with
`A' = g⁻¹𝒪_{𝒞'}`, `A = g⁻¹𝒪_𝒞`, `S = g⁻¹f⁻¹𝒪_ℬ`, `B' = 𝒪_{𝒟'}`, `B = 𝒪_𝒟`, with `π` the
inverse image of the reduction and `q` the inverse-image form `g^♯` of the structure map
of `g`. -/
def toData : Stacks.Deformation.InverseImageExtension.Data
    ((invImage g).obj (baseRing f)) ((invImage g).obj X.O) ((invImage g).obj d.OC')
    Y.O d.OD' where
  π := d.invReduction
  locallySurjective_π :=
    isLocallySurjective_invImage_map g d.reduction d.locallySurjective_reduction
  N := d.G
  c := d.c
  q := g.fSharpInverseImage
  p := d.p
  locallySurjective_p := d.locallySurjective_p
  ι := d.ι
  inr_mul_inr := d.inr_mul_inr
  smul_inr := d.smul_inr
  u := (invImage g).map d.fromBase
  v := d.fromBaseBack
  base_comm := by simpa only [Functor.map_comp] using d.base_comm

/-! ### The two thickened ringed topoi and the morphism between them -/

/-- The thickened source ringed topos `(Sh(𝒟), 𝒪_{𝒟'})`. -/
abbrev thickenedSource : RingedTopos.{u, u, u} := { C := Y.C, J := Y.J, O := d.OD' }

/-- The thickened target ringed topos `(Sh(𝒞), 𝒪_{𝒞'})`. -/
abbrev thickenedTarget : RingedTopos.{u, u, u} := { C := X.C, J := X.J, O := d.OC' }

/-- **A morphism of ringed topoi `(Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})` inducing `g` on the
underlying topoi is the same datum as a comorphism `g⁻¹𝒪_{𝒞'} ⟶ 𝒪_{𝒟'}` of sheaves of
commutative rings**: its structure map `𝒪_{𝒞'} ⟶ g_*𝒪_{𝒟'}` and that comorphism are adjunct
under `g⁻¹ ⊣ g_*`. -/
def ringedToposHomEquiv :
    ((invImage g).obj d.OC' ⟶ d.OD') ≃
      (d.OC' ⟶ (pushforwardCommRingFunctor g.toToposHom).obj d.OD') :=
  (commRingImageAdjunction g.toToposHom).homEquiv d.OC' d.OD'

/-- The morphism of ringed topoi `(Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})` attached to a comorphism
`g⁻¹𝒪_{𝒞'} ⟶ 𝒪_{𝒟'}`: it induces `g` on the underlying topoi and its structure map is the
adjunct of the comorphism. -/
def toRingedToposHom (φ : (invImage g).obj d.OC' ⟶ d.OD') :
    RingedToposHom d.thickenedSource d.thickenedTarget :=
  { toToposHom := g.toToposHom
    fSharp := d.ringedToposHomEquiv φ }

omit [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [X.J.HasSheafCompose (forget CommRingCat.{u})] in
/-- The morphism of ringed topoi attached to a comorphism induces `g` on the underlying
topoi. -/
theorem toRingedToposHom_toToposHom (φ : (invImage g).obj d.OC' ⟶ d.OD') :
    (d.toRingedToposHom φ).toToposHom = g.toToposHom := rfl

omit [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [X.J.HasSheafCompose (forget CommRingCat.{u})] in
/-- The structure map of the morphism of ringed topoi attached to a comorphism is the adjunct of
that comorphism. -/
theorem toRingedToposHom_fSharp (φ : (invImage g).obj d.OC' ⟶ d.OD') :
    (d.toRingedToposHom φ).fSharp = d.ringedToposHomEquiv φ := rfl

omit [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [X.J.HasSheafCompose (forget CommRingCat.{u})] in
/-- The inverse-image form of the structure map of the morphism of ringed topoi attached to a
comorphism is that comorphism. -/
theorem fSharpInverseImage_toRingedToposHom (φ : (invImage g).obj d.OC' ⟶ d.OD') :
    (d.toRingedToposHom φ).fSharpInverseImage = φ :=
  d.ringedToposHomEquiv.symm_apply_apply φ

omit [Y.J.HasSheafCompose (forget CommRingCat.{u})]
  [X.J.HasSheafCompose (forget CommRingCat.{u})] in
/-- Every morphism of ringed topoi `(Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})` inducing `g` on the
underlying topoi comes from a comorphism `g⁻¹𝒪_{𝒞'} ⟶ 𝒪_{𝒟'}`. -/
theorem exists_toRingedToposHom_eq
    (ψ : d.OC' ⟶ (pushforwardCommRingFunctor g.toToposHom).obj d.OD') :
    ∃ φ : (invImage g).obj d.OC' ⟶ d.OD', d.toRingedToposHom φ =
      { toToposHom := g.toToposHom, fSharp := ψ } :=
  ⟨d.ringedToposHomEquiv.symm ψ, by
    rw [toRingedToposHom, d.ringedToposHomEquiv.apply_symm_apply]⟩

/-! ### The pullback extension `𝒪'₂ = 𝒪_{𝒟'} ×_{𝒪_𝒟} g⁻¹𝒪_𝒞` -/

/-- **Stacks 0GQ8, the second construction.**  Pulling the extension
`0 ⟶ 𝒢 ⟶ 𝒪_{𝒟'} ⟶ 𝒪_𝒟 ⟶ 0` back along `g^♯ : g⁻¹𝒪_𝒞 ⟶ 𝒪_𝒟` gives an extension
`0 ⟶ 𝒢 ⟶ 𝒪'₂ ⟶ g⁻¹𝒪_𝒞 ⟶ 0` of `g⁻¹f⁻¹𝒪_ℬ`-algebras, with
`𝒪'₂ = 𝒪_{𝒟'} ×_{𝒪_𝒟} g⁻¹𝒪_𝒞` the fibre product of sheaves of rings and the remark's second
displayed diagram its two projections. -/
@[stacks 0GQ8 "the pullback extension 𝒪'₂ = 𝒪_{𝒟'} ×_{𝒪_𝒟} g⁻¹𝒪_𝒞 along g^♯, with the second \
displayed diagram its projections. Carried: that 𝒢 is the square-zero ideal of 𝒪_{𝒟'} with its \
𝒪_𝒟-action (Data.ι, Data.inr_mul_inr, Data.smul_inr). NOT carried: that g⁻¹𝒪_{𝒞'} is an \
extension of g⁻¹𝒪_𝒞 by g⁻¹ℱ -- the ideal is the kernel ideal of g⁻¹(reduction) and local \
surjectivity is isLocallySurjective_invImage_map"]
def pullbackExtension :
    AlgebraExtension ((invImage g).obj (baseRing f)) ((invImage g).obj X.O) d.invBase
      d.G.val.presheaf :=
  d.toData.pullbackExtension

/-! ### The pushout extension `𝒪'₁` -/

/-- **Stacks 0GQ8, the first construction.**  Pushing the extension
`0 ⟶ g⁻¹ℱ ⟶ g⁻¹𝒪_{𝒞'} ⟶ g⁻¹𝒪_𝒞 ⟶ 0` out along `c : g⁻¹ℱ ⟶ 𝒢` gives an extension
`0 ⟶ 𝒢 ⟶ 𝒪'₁ ⟶ g⁻¹𝒪_𝒞 ⟶ 0` of `g⁻¹f⁻¹𝒪_ℬ`-algebras, with the remark's first displayed diagram
its comparison with `g⁻¹𝒪_{𝒞'}`. -/
@[stacks 0GQ8 "the pushout extension 𝒪'₁ of g⁻¹𝒪_{𝒞'} along c : g⁻¹ℱ ⟶ 𝒢, with the first \
displayed diagram its comparison with g⁻¹𝒪_{𝒞'}. Carried: that 𝒢 is the square-zero ideal of \
𝒪_{𝒟'}. NOT carried: that g⁻¹𝒪_{𝒞'} is an extension of g⁻¹𝒪_𝒞 by g⁻¹ℱ -- the ideal is the \
kernel ideal of g⁻¹(reduction), whose identification with g⁻¹ℱ is the left exactness of g⁻¹, \
and local surjectivity is isLocallySurjective_invImage_map"]
def pushoutExtension [HasWeakSheafify Y.J CommRingCat.{u}]
    [Y.J.WEqualsLocallyBijective CommRingCat.{u}] :
    AlgebraExtension ((invImage g).obj (baseRing f)) ((invImage g).obj X.O) d.invBase
      d.G.val.presheaf :=
  d.toData.pushoutExtension

/-! ### The criterion of Stacks 0GQ8 -/

/-- A morphism `g' : (Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})` of ringed topoi over `(Sh(ℬ), 𝒪_ℬ)`
compatible with `g` and `c`, in its comorphism form: a morphism `g⁻¹𝒪_{𝒞'} ⟶ 𝒪_{𝒟'}` of
`g⁻¹f⁻¹𝒪_ℬ`-algebras which lies over `g^♯` and whose restriction to the ideal `g⁻¹ℱ` is `c`.
The morphism of ringed topoi it is, is `Data.compatibleRingedToposHom`. -/
abbrev CompatibleHom := d.toData.CompatibleHom

/-- **The morphism of ringed topoi `g' : (Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})`** attached to a
compatible comorphism. -/
def compatibleRingedToposHom (h : d.CompatibleHom) :
    RingedToposHom d.thickenedSource d.thickenedTarget :=
  d.toRingedToposHom h.hom

/-- The inverse-image form of the structure map of `g'` is the comorphism it comes from. -/
theorem fSharpInverseImage_compatibleRingedToposHom (h : d.CompatibleHom) :
    (d.compatibleRingedToposHom h).fSharpInverseImage = h.hom :=
  d.fSharpInverseImage_toRingedToposHom h.hom

/-- **`g'` lies over `(Sh(ℬ), 𝒪_ℬ)`**: its comorphism carries the `g⁻¹f⁻¹𝒪_ℬ`-algebra structure
of `g⁻¹𝒪_{𝒞'}` to that of `𝒪_{𝒟'}`. -/
theorem compatibleRingedToposHom_base (h : d.CompatibleHom) :
    (invImage g).map d.fromBase ≫ (d.compatibleRingedToposHom h).fSharpInverseImage
      = d.fromBaseBack :=
  d.fSharpInverseImage_compatibleRingedToposHom h ▸ h.base_comm

/-- **`g'` lies over `g`**: its comorphism followed by the reduction `𝒪_{𝒟'} ⟶ 𝒪_𝒟` is
`g⁻¹`(reduction) followed by `g^♯`. -/
theorem compatibleRingedToposHom_comp_p (h : d.CompatibleHom) :
    (d.compatibleRingedToposHom h).fSharpInverseImage ≫ d.p
      = d.invReduction ≫ g.fSharpInverseImage :=
  d.fSharpInverseImage_compatibleRingedToposHom h ▸ h.proj_comm

/-- **`g'` is compatible with `c`**: its comorphism restricts to `c` on the ideal
`g⁻¹ℱ = Ker (g⁻¹(reduction))`. -/
theorem compatibleRingedToposHom_kernel (h : d.CompatibleHom) (U : Y.Cᵒᵖ)
    (s : ↥(kernelIdeal d.invReduction.hom U)) :
    (d.compatibleRingedToposHom h).fSharpInverseImage.hom.app U
        (s : ↥(((invImage g).obj d.OC').obj.obj U))
      = d.ι.app U (d.c.app U s) :=
  d.fSharpInverseImage_compatibleRingedToposHom h ▸ h.kernel_comm U s

/-- **Stacks Project, Tag 0GQ8, the criterion.**  A morphism
`g' : (Sh(𝒟), 𝒪_{𝒟'}) ⟶ (Sh(𝒞), 𝒪_{𝒞'})` of ringed topoi over `(Sh(ℬ), 𝒪_ℬ)` compatible with
`g` and `c` exists if and only if the pushout `𝒪'₁` and the pullback `𝒪'₂` are isomorphic as
`g⁻¹f⁻¹𝒪_ℬ`-algebra extensions of `g⁻¹𝒪_𝒞` by `𝒢`.

The morphisms `g'` are the comorphisms of `Data.CompatibleHom`, which really are morphisms of
ringed topoi between the two thickenings by `Data.compatibleRingedToposHom`, with the three
compatibilities of the source read off in `Data.compatibleRingedToposHom_base`,
`Data.compatibleRingedToposHom_comp_p` and `Data.compatibleRingedToposHom_kernel`. -/
@[stacks 0GQ8 "the diagram chase: a morphism g' : (Sh(D), O_{D'}) ⟶ (Sh(C), O_{C'}) of ringed \
topoi over (Sh(B), O_B) compatible with g and c exists iff 𝒪'₁ ≅ 𝒪'₂ as g⁻¹f⁻¹O_B-algebra \
extensions of g⁻¹O_C by 𝒢; g' is in comorphism form, a morphism of ringed topoi inducing g by \
Data.ringedToposHomEquiv and Data.compatibleRingedToposHom. Carried: 𝒢 is the square-zero ideal \
of O_{D'}. NOT included: the remark's second half, identifying 𝒪'₁ with ξ and 𝒪'₂ with ζ"]
theorem nonempty_compatibleHom_iff_isomorphic [HasWeakSheafify Y.J CommRingCat.{u}]
    [Y.J.WEqualsLocallyBijective CommRingCat.{u}] :
    Nonempty d.CompatibleHom ↔
      AlgebraExtension.Isomorphic d.pushoutExtension d.pullbackExtension :=
  d.toData.nonempty_compatibleHom_iff_isomorphic

end Data

end Deformation.ToposThickening.InverseImageExtension

end
