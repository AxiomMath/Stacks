module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEtaleBaseDerivation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleObjDerivation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsSheafification
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget

/-!
# **Stacks 04CS**: the canonical isomorphism `(Ω_{X/Y})^a ≅ Ω_{X_étale/Y_étale}`

Let `f : X ⟶ Y` be a morphism of schemes of a big étale site `B`.  Stacks 04CS asserts a
canonical isomorphism between the small-étale sheaf `(Ω_{X/Y})^a` associated to the quasi-coherent
module of relative differentials and the module of differentials
`Ω_{X_étale/Y_étale}` of the induced morphism of small étale ringed topoi, compatible with the
universal derivations.  This module proves it.

Both sides corepresent one functor, the `Y_étale`-derivations of `𝒪_{X_étale}`:

* `Ω_{X_étale/Y_étale}` does by construction
  (`AlgebraicGeometry.SmallEtale.sheafOfDifferentialsCorepresentableBy`);
* `(Ω_{X/Y})^a` with `d^a` corepresents the derivations of `𝒪_{X_étale}` which annihilate the
  functions pulled back from the *opens* of `Y`
  (`AlgebraicGeometry.SmallEtale.existsUnique_postcomp_associatedDerivation`), and **the two
  classes of derivations are the same class**, which is what this module establishes.

So the isomorphism is `AlgebraicGeometry.SheafOfModules.corepresentableByIso` applied to the two
corepresentations, and its compatibility with the universal derivations is the defining equation
of that comparison.

## The comparison of the two classes of derivations

The vanishing condition of Stacks 04BN for `Ω_{X_étale/Y_étale}` is over
`f_small^♯ : f_small^{-1}𝒪_{Y_étale} ⟶ 𝒪_{X_étale}`, whose sections are not given by a formula.
What replaces a formula is the adjunction `f_small^{-1} ⊣ f_{small,*}` for sheaves of *sets*,
under which the two forms of the structure map are adjunct: a derivation annihilates the image of
`f_small^♯` exactly when its direct image annihilates the image of the direct-image form
`AlgebraicGeometry.structureSharp`, and *there* the sections are given by a formula — at an étale
`V / Y` the structure map pulls a global function on `V` back along the projection
`X ×_Y V ⟶ V`.  Both directions of that transposition are proved here, generically for a morphism
of ringed topoi.

With the vanishing in direct-image form, the two inclusions are:

* a `Y_étale`-derivation annihilates every function pulled back from an open `W` of `Y`, because
  `W` is in particular étale over `Y` and the section
  `AlgebraicGeometry.SmallEtale.pullbackSection` is the direct-image structure map at the object
  `W` of `Y_étale`, restricted along the identification of `f⁻¹W` with the base change `X ×_Y W`
  (`AlgebraicGeometry.SmallEtale.topIso_inv_appTop_baseChangeOpens`);
* `d^a` is a `Y_étale`-derivation, because it annihilates every global function pulled back from a
  scheme étale over `Y` along a morphism over `Y`
  (`AlgebraicGeometry.SmallEtale.associatedDerivation_etaleBase_eq_zero`), and the base-change
  projection `X ×_Y V ⟶ V` is such a morphism.

## Main definitions

* `AlgebraicGeometry.SmallEtale.derivationSetHom` and
  `AlgebraicGeometry.SmallEtale.zeroSetHom` read a derivation and the zero derivation as
  morphisms of the underlying sheaves of sets, the form the adjunction applies to.
* `AlgebraicGeometry.SmallEtale.etaleAssociatedDerivation` is `d^a` as a `Y_étale`-derivation, and
  `AlgebraicGeometry.SmallEtale.ofEtaleDerivation` reads a `Y_étale`-derivation over the constant
  presheaf of rings `ℤ`.
* `AlgebraicGeometry.SmallEtale.differentialsIso` is **the canonical isomorphism of Stacks
  04CS**, and `AlgebraicGeometry.SmallEtale.universalDifferentialsComparison` is the comparison
  map `c''` of the source's proof at `𝓕 = Ω_{X_étale/Y_étale}`.

## Main results

* `AlgebraicGeometry.RingedToposHom.fSharpInverseImageForget_comp_eq_of_fSharp_comp_eq` and
  `AlgebraicGeometry.RingedToposHom.fSharp_comp_eq_of_fSharpInverseImageForget_comp_eq`: the two
  directions of the transposition, for an arbitrary morphism of ringed topoi.
* `AlgebraicGeometry.SmallEtale.d_etaleStructureMap_eq_zero` and
  `AlgebraicGeometry.SmallEtale.d_structureSharp_eq_zero`: the transposition carried out for the
  small étale ringed topoi of a morphism of schemes.
* `AlgebraicGeometry.SmallEtale.d_pullbackSection_eq_zero` and
  `AlgebraicGeometry.SmallEtale.etaleAssociatedDerivation`: the two inclusions between the
  classes of derivations.
* `AlgebraicGeometry.SmallEtale.existsUnique_postcomp_etaleAssociatedDerivation`: `(Ω_{X/Y})^a`
  with `d^a` corepresents the `Y_étale`-derivations.
* `AlgebraicGeometry.SmallEtale.postcomp_differentialsIso_hom`: the isomorphism carries `d^a` to
  `d_{X_étale/Y_étale}`, which is the compatibility with universal derivations that 04CS asserts.
* `AlgebraicGeometry.SmallEtale.differentialsIso_hom_eq` and
  `AlgebraicGeometry.SmallEtale.isIso_universalDifferentialsComparison`: the isomorphism *is* the
  comparison map `c''` of `AlgebraicGeometry.SmallEtale.differentialsComparison`, so the map the
  source's proof produces is the invertible one.

## Implementation notes

The source's proof builds two maps `c` and `c''` and asserts that they are mutually inverse,
leaving the verification to the reader.  Here the two maps are not built separately: both sides
are exhibited as corepresenting objects of one functor, and the isomorphism together with the
fact that its two composites are identities is `corepresentableByIso`.  The comparison map `c''`
of the source's proof is `AlgebraicGeometry.SmallEtale.differentialsComparison`, and the two
composites being identities is
`AlgebraicGeometry.SmallEtale.associatedDerivation_postcomp_differentialsComparison` together
with `AlgebraicGeometry.SmallEtale.postcomp_associatedDerivation_injective`; those are what
`existsUnique_postcomp_associatedDerivation` packages, so nothing of the source's argument is
bypassed.

The setting is `X Y : AlgebraicGeometry.BigEtaleSite.Scheme` rather than the
`AlgebraicGeometry.BigEtaleSite.Contains X` of the other Stacks 04CS files: the morphism of small
étale ringed topoi `AlgebraicGeometry.smallEtaleRingedToposHom` needs the small étale site of `Y`
as well, which the tag's `Ω_{X_étale/Y_étale}` presupposes.

Nothing identifies the base sheaf `f_small^{-1}𝒪_{Y_étale}` with the `ε^{-1}f^{-1}𝒪_Y` of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleRelativeDerivation.lean`, and
nothing needs to: only the two *classes of derivations* enter the universal properties, and the
transposition above compares them directly.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04BN](https://stacks.math.columbia.edu/tag/04BN), the module of
  differentials of a homomorphism of sheaves of rings on a site, and
  [Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), its universal property.
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R), the morphism of small
  étale ringed sites and ringed topoi of a morphism of schemes.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), the associated module on
  the small étale site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w v' u' w'

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **The transposition of the two forms of the structure map**, with a morphism out of `𝒪_C`
appended: the adjunct of `f♯ : f⁻¹𝒪_D ⟶ 𝒪_C` followed by `δ` is `f♯ : 𝒪_D ⟶ f_*𝒪_C` followed by
the direct image of `δ`. -/
public theorem homEquiv_fSharpInverseImageForget_comp (f : RingedToposHom X Y)
    {E : X.Topos} (δ : X.forgetRing.obj X.O ⟶ E) :
    f.toToposHom.adj.homEquiv (Y.forgetRing.obj Y.O) E
        (f.fSharpInverseImageForget ≫ δ) =
      forgetFSharp f ≫ f.toToposHom.pushforward.map δ := by
  have h0 : f.toToposHom.adj.homEquiv (Y.forgetRing.obj Y.O) (X.forgetRing.obj X.O)
      f.fSharpInverseImageForget = forgetFSharp f := Equiv.apply_symm_apply _ _
  refine Eq.trans (f.toToposHom.adj.homEquiv_naturality_right _ δ) ?_
  exact congrArg (fun m => m ≫ f.toToposHom.pushforward.map δ) h0

/-- **Two morphisms out of `𝒪_C` agree after `f♯ : f⁻¹𝒪_D ⟶ 𝒪_C` as soon as their direct images
agree after `f♯ : 𝒪_D ⟶ f_*𝒪_C`.**  The two forms of the structure map are adjunct under
`f⁻¹ ⊣ f_*` for sheaves of sets, so this is the naturality of that adjunction. -/
public theorem fSharpInverseImageForget_comp_eq_of_fSharp_comp_eq (f : RingedToposHom X Y)
    {E : X.Topos} (ε ε' : X.forgetRing.obj X.O ⟶ E)
    (h : forgetFSharp f ≫ f.toToposHom.pushforward.map ε =
      forgetFSharp f ≫ f.toToposHom.pushforward.map ε') :
    f.fSharpInverseImageForget ≫ ε = f.fSharpInverseImageForget ≫ ε' := by
  refine (f.toToposHom.adj.homEquiv (Y.forgetRing.obj Y.O) E).injective ?_
  exact (homEquiv_fSharpInverseImageForget_comp f ε).trans
    (h.trans (homEquiv_fSharpInverseImageForget_comp f ε').symm)

/-- **The converse transposition:** the direct images of two morphisms out of `𝒪_C` agree after
`f♯ : 𝒪_D ⟶ f_*𝒪_C` as soon as the morphisms agree after `f♯ : f⁻¹𝒪_D ⟶ 𝒪_C`. -/
public theorem fSharp_comp_eq_of_fSharpInverseImageForget_comp_eq (f : RingedToposHom X Y)
    {E : X.Topos} (ε ε' : X.forgetRing.obj X.O ⟶ E)
    (h : f.fSharpInverseImageForget ≫ ε = f.fSharpInverseImageForget ≫ ε') :
    forgetFSharp f ≫ f.toToposHom.pushforward.map ε =
      forgetFSharp f ≫ f.toToposHom.pushforward.map ε' :=
  (homEquiv_fSharpInverseImageForget_comp f ε).symm.trans
    ((congrArg (f.toToposHom.adj.homEquiv (Y.forgetRing.obj Y.O) E) h).trans
      (homEquiv_fSharpInverseImageForget_comp f ε'))

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  {F : SheafOfModules.{u} (structureSheaf B X.obj X.property)}
  {R : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ CommRingCat.{u}}
  {ψ : R ⟶ (commRingStructureSheaf B X.obj X.property).obj}
  (D : PresheafOfModules.Derivation'
    (R := (commRingStructureSheaf B X.obj X.property).obj) F.val ψ)

/-- A derivation of `𝒪_{X_étale}`, read as a morphism of the underlying sheaves of sets.  This
is the form in which the adjunction `f_small^{-1} ⊣ f_{small,*}` applies to it. -/
public noncomputable def derivationSetHom :
    (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property)).forgetRing.obj
        (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property)).O ⟶
      Sheaf.moduleSheaf.{u, u, u + 1} (structureSheaf B X.obj X.property) F :=
  Sheaf.unaryOpHom (fun _ a => D.d a) (fun g a => (D.d_map g a).symm)

/-- The zero derivation, read as a morphism of the underlying sheaves of sets. -/
public noncomputable def zeroSetHom
    (F : SheafOfModules.{u} (structureSheaf B X.obj X.property)) :
    (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property)).forgetRing.obj
        (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property)).O ⟶
      Sheaf.moduleSheaf.{u, u, u + 1} (structureSheaf B X.obj X.property) F :=
  Sheaf.unaryOpHom (fun V _ => (0 : F.val.obj V)) (fun g _ => (F.val.map g).hom.map_zero)

/-- The structure map of `f_small` in inverse-image form, read on underlying sheaves of sets, is
the adjunct of its direct-image form. -/
public theorem forgetRing_map_etaleStructureMap :
    (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property)).forgetRing.map
        (etaleStructureMap B f) =
      (smallEtaleRingedToposHom B f).fSharpInverseImageForget :=
  RingedToposHom.forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget
    (smallEtaleRingedToposHom B f)

/-- The direct image of `AlgebraicGeometry.SmallEtale.derivationSetHom`, precomposed with the
direct-image form of the structure map, computed on sections: over an étale `V / Y` it is the
derivation applied to the pullback of a global function on `V` along the base-change projection
`X ×_Y V ⟶ V`. -/
public theorem forgetFSharp_comp_derivationSetHom_app
    (V : (SmallEtale B Y.obj Y.property)ᵒᵖ)
    (t : (commRingStructureSheaf B Y.obj Y.property).obj.obj V) :
    (RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B f) ≫
        (smallEtaleRingedToposHom B f).toToposHom.pushforward.map
          (derivationSetHom B D)).hom.app V t =
      D.d (X := op ((smallEtaleBaseChange B f).obj V.unop))
        (((structureSharp B f).hom.app V).hom t) :=
  rfl

/-- The same for the zero morphism: it is zero. -/
public theorem forgetFSharp_comp_zeroSetHom_app
    (V : (SmallEtale B Y.obj Y.property)ᵒᵖ)
    (t : (commRingStructureSheaf B Y.obj Y.property).obj.obj V) :
    (RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B f) ≫
        (smallEtaleRingedToposHom B f).toToposHom.pushforward.map
          (zeroSetHom B F)).hom.app V t =
      (0 : F.val.obj (op ((smallEtaleBaseChange B f).obj V.unop))) :=
  rfl

/-- `AlgebraicGeometry.SmallEtale.derivationSetHom` precomposed with the inverse-image form of
the structure map, computed on sections: it is the derivation applied to the image of a section
of `f_small^{-1}𝒪_{Y_étale}` under `f_small^♯`. -/
public theorem fSharpInverseImageForget_comp_derivationSetHom_app
    (V : (SmallEtale B X.obj X.property)ᵒᵖ)
    (s : (etaleInverseImageStructureSheaf B f).obj.obj V) :
    ((smallEtaleRingedToposHom B f).fSharpInverseImageForget ≫
        derivationSetHom B D).hom.app V s =
      D.d (((etaleStructureMap B f).hom.app V).hom s) := by
  rw [← forgetRing_map_etaleStructureMap B f]
  rfl

/-- The same for the zero morphism: it is zero. -/
public theorem fSharpInverseImageForget_comp_zeroSetHom_app
    (V : (SmallEtale B X.obj X.property)ᵒᵖ)
    (s : (etaleInverseImageStructureSheaf B f).obj.obj V) :
    ((smallEtaleRingedToposHom B f).fSharpInverseImageForget ≫
        zeroSetHom B F).hom.app V s = (0 : F.val.obj V) := by
  rw [← forgetRing_map_etaleStructureMap B f]
  rfl

/-- **A derivation of `𝒪_{X_étale}` which annihilates the global functions pulled back along the
base-change projections annihilates the whole image of `f_small^♯`,** so it is a
`Y_étale`-derivation in the sense of Stacks 04BN.

The sections of `f_small^{-1}𝒪_{Y_étale}` are not given by a formula; what replaces a formula is
the adjunction `f_small^{-1} ⊣ f_{small,*}` for sheaves of sets, under which the two forms of the
structure map are adjunct.  The hypothesis is the vanishing in direct-image form, where the
sections *are* given by a formula, and
`AlgebraicGeometry.RingedToposHom.fSharpInverseImageForget_comp_eq_of_fSharp_comp_eq` transposes
it. -/
public theorem d_etaleStructureMap_eq_zero
    (h : ∀ (V : (SmallEtale B Y.obj Y.property)ᵒᵖ)
        (t : (commRingStructureSheaf B Y.obj Y.property).obj.obj V),
      D.d (X := op ((smallEtaleBaseChange B f).obj V.unop))
        (((structureSharp B f).hom.app V).hom t) = 0)
    (V : (SmallEtale B X.obj X.property)ᵒᵖ)
    (s : (etaleInverseImageStructureSheaf B f).obj.obj V) :
    D.d (((etaleStructureMap B f).hom.app V).hom s) = 0 := by
  have hset : (smallEtaleRingedToposHom B f).fSharpInverseImageForget ≫ derivationSetHom B D =
      (smallEtaleRingedToposHom B f).fSharpInverseImageForget ≫ zeroSetHom B F := by
    refine RingedToposHom.fSharpInverseImageForget_comp_eq_of_fSharp_comp_eq
      (smallEtaleRingedToposHom B f) (derivationSetHom B D) (zeroSetHom B F) ?_
    ext W t
    refine Eq.trans (forgetFSharp_comp_derivationSetHom_app B f D W t) ?_
    exact Eq.trans (h W t) (forgetFSharp_comp_zeroSetHom_app B f (F := F) W t).symm
  refine Eq.trans (fSharpInverseImageForget_comp_derivationSetHom_app B f D V s).symm ?_
  refine Eq.trans (congrArg
    (fun m : (smallEtaleRingedToposHom B f).toToposHom.inverseImage.obj
        ((RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)).forgetRing.obj
          (commRingStructureSheaf B Y.obj Y.property)) ⟶
      Sheaf.moduleSheaf.{u, u, u + 1} (structureSheaf B X.obj X.property) F =>
      m.hom.app V s) hset) ?_
  exact fSharpInverseImageForget_comp_zeroSetHom_app B f V s

/-- **The converse.**  A `Y_étale`-derivation of `𝒪_{X_étale}` annihilates the global functions
pulled back along the base-change projections.  This is the same transposition read in the other
direction. -/
public theorem d_structureSharp_eq_zero
    (h : ∀ (V : (SmallEtale B X.obj X.property)ᵒᵖ)
        (s : (etaleInverseImageStructureSheaf B f).obj.obj V),
      D.d (((etaleStructureMap B f).hom.app V).hom s) = 0)
    (V : (SmallEtale B Y.obj Y.property)ᵒᵖ)
    (t : (commRingStructureSheaf B Y.obj Y.property).obj.obj V) :
    D.d (X := op ((smallEtaleBaseChange B f).obj V.unop))
      (((structureSharp B f).hom.app V).hom t) = 0 := by
  have hset : RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B f) ≫
        (smallEtaleRingedToposHom B f).toToposHom.pushforward.map (derivationSetHom B D) =
      RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B f) ≫
        (smallEtaleRingedToposHom B f).toToposHom.pushforward.map (zeroSetHom B F) := by
    refine RingedToposHom.fSharp_comp_eq_of_fSharpInverseImageForget_comp_eq
      (smallEtaleRingedToposHom B f) (derivationSetHom B D) (zeroSetHom B F) ?_
    ext W s
    refine Eq.trans (fSharpInverseImageForget_comp_derivationSetHom_app B f D W s) ?_
    exact Eq.trans (h W s) (fSharpInverseImageForget_comp_zeroSetHom_app B f (F := F) W s).symm
  refine Eq.trans (forgetFSharp_comp_derivationSetHom_app B f D V t).symm ?_
  refine Eq.trans (congrArg
    (fun m : (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)).forgetRing.obj
        (commRingStructureSheaf B Y.obj Y.property) ⟶
      (smallEtaleRingedToposHom B f).toToposHom.pushforward.obj
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureSheaf B X.obj X.property) F) =>
      m.hom.app V t) hset) ?_
  exact forgetFSharp_comp_zeroSetHom_app B f (F := F) V t

/-! ### The two classes of derivations coincide -/

/-- **`d^a` annihilates the functions pulled back along the base-change projections.**  Over an
étale `V / Y` the structure map pulls a global function on `V` back along `X ×_Y V ⟶ V`, and
`X ×_Y V ⟶ V` is a morphism over `Y` out of an object of the small étale site of `X` into a
scheme étale over `Y`, so this is
`AlgebraicGeometry.SmallEtale.associatedDerivation_etaleBase_eq_zero`. -/
public theorem associatedDerivation_structureSharp_eq_zero
    (V : (SmallEtale B Y.obj Y.property)ᵒᵖ)
    (t : (commRingStructureSheaf B Y.obj Y.property).obj.obj V) :
    (associatedDerivation B X.property (schemeHom B f)).d
        (X := op ((smallEtaleBaseChange B f).obj V.unop))
        (((structureSharp B f).hom.app V).hom t) = 0 :=
  associatedDerivation_etaleBase_eq_zero B X.property (schemeHom B f)
    (objHom B Y.obj Y.property V.unop) (op ((smallEtaleBaseChange B f).obj V.unop))
    (B.inclusion.map (pullback.fst V.unop.obj.hom f))
    (((B.inclusion.map_comp _ _).symm.trans
      (congrArg B.inclusion.map pullback.condition)).trans (B.inclusion.map_comp _ _)) t

/-- **The functions pulled back from an open of `Y` are the structure map at that open.**  The
section `AlgebraicGeometry.SmallEtale.pullbackSection` attached to `b ∈ Γ(Y, W)` is the
direct-image form of the structure map at the object of the small étale site of `Y` given by
`W`, applied to `b` read as a global function on the open subscheme `W`, and then restricted
along the identification of `f⁻¹W` with the base change `X ×_Y W`. -/
public theorem map_structureSharp_opens_eq_pullbackSection (W : Y.obj.Opens) (b : Γ(Y.obj, W)) :
    (commRingStructureSheaf B X.obj X.property).obj.map
        ((baseChangeOpensObjIso B f W).hom).op
        (((structureSharp B f).hom.app
          (op ((opensToSmallEtale B Y.obj Y.property).obj W))).hom
            ((Scheme.Opens.topIso W).inv.hom b)) =
      pullbackSection B X.property (schemeHom B f) W b := by
  have h := congrArg (fun m : CommRingCat.Hom _ _ => m.hom b)
    (topIso_inv_appTop_baseChangeOpens B f W)
  exact h

/-- **A `Y_étale`-derivation of `𝒪_{X_étale}` annihilates every function pulled back from an
open of `Y`,** which is the hypothesis under which `(Ω_{X/Y})^a` with `d^a` is universal
(`AlgebraicGeometry.SmallEtale.existsUnique_postcomp_associatedDerivation`).

An open of `Y` is in particular étale over `Y`, so the vanishing in direct-image form is
available at that object by `AlgebraicGeometry.SmallEtale.d_structureSharp_eq_zero`; restricting
along the identification of `f⁻¹W` with `X ×_Y W` and using
`AlgebraicGeometry.SmallEtale.map_structureSharp_opens_eq_pullbackSection` gives the
vanishing. -/
public theorem d_pullbackSection_eq_zero
    (h : ∀ (V : (SmallEtale B X.obj X.property)ᵒᵖ)
        (s : (etaleInverseImageStructureSheaf B f).obj.obj V),
      D.d (((etaleStructureMap B f).hom.app V).hom s) = 0)
    (W : Y.obj.Opens) (b : Γ(Y.obj, W)) :
    D.d (pullbackSection B X.property (schemeHom B f) W b) = 0 := by
  have h0 := d_structureSharp_eq_zero B f D h
    (op ((opensToSmallEtale B Y.obj Y.property).obj W)) ((Scheme.Opens.topIso W).inv.hom b)
  rw [← map_structureSharp_opens_eq_pullbackSection B f W b]
  refine Eq.trans (D.d_map ((baseChangeOpensObjIso B f W).hom).op _) ?_
  exact Eq.trans (congrArg _ h0) (map_zero _)

/-! ### The canonical isomorphism -/

/-- **A `Y_étale`-derivation, read as a derivation over the constant presheaf of rings `ℤ`:**
the same values, with only the Leibniz rule recorded.  This is the form in which
`AlgebraicGeometry.SmallEtale.existsUnique_postcomp_associatedDerivation` consumes it. -/
public noncomputable def ofEtaleDerivation
    {F : SheafOfModules.{u} (structureSheaf B X.obj X.property)} (D : EtaleDerivation B f F) :
    PresheafOfModules.Derivation'
      (R := (commRingStructureSheaf B X.obj X.property).obj) F.val
      (siteConstIntMap B X.property _) where
  d := D.d
  d_mul := D.d_mul
  d_map := D.d_map
  d_app {V} a :=
    siteConstIntMap_app_eq_zero (P := (commRingStructureSheaf B X.obj X.property).obj)
      B X.property D.d (D.d_one V) a

/-- **`d^a` as a `Y_étale`-derivation of `𝒪_{X_étale}`.**  The values of
`AlgebraicGeometry.SmallEtale.associatedDerivation`; what is added is the vanishing condition of
Stacks 04BN over `f_small^♯`, which
`AlgebraicGeometry.SmallEtale.associatedDerivation_structureSharp_eq_zero` and
`AlgebraicGeometry.SmallEtale.d_etaleStructureMap_eq_zero` supply. -/
public noncomputable def etaleAssociatedDerivation :
    EtaleDerivation B f (associatedRelativeDifferentials B X.property (schemeHom B f)) where
  d := (associatedDerivation B X.property (schemeHom B f)).d
  d_mul := (associatedDerivation B X.property (schemeHom B f)).d_mul
  d_map := (associatedDerivation B X.property (schemeHom B f)).d_map
  d_app {V} a :=
    d_etaleStructureMap_eq_zero B f (associatedDerivation B X.property (schemeHom B f))
      (associatedDerivation_structureSharp_eq_zero B f) V a

/-- Two derivations with the same values on every section are equal. -/
private theorem derivation_ext_of_d_eq {C : Type*} [Category C] {S R : Cᵒᵖ ⥤ CommRingCat.{u}}
    {M : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)} {φ : S ⟶ R}
    {d d' : M.Derivation' φ} (h : ∀ {V : Cᵒᵖ} (a : R.obj V), d.d a = d'.d a) : d = d' :=
  PresheafOfModules.Derivation.ext (funext fun _ => AddMonoidHom.ext h)

/-- **`(Ω_{X/Y})^a` with `d^a` corepresents the `Y_étale`-derivations of `𝒪_{X_étale}`.**

This is `AlgebraicGeometry.SmallEtale.existsUnique_postcomp_associatedDerivation` with its
hypothesis replaced by the vanishing condition of Stacks 04BN over `f_small^♯`.  The two are
interchangeable: a `Y_étale`-derivation annihilates the functions pulled back from an open of
`Y` by `AlgebraicGeometry.SmallEtale.d_pullbackSection_eq_zero`, and `d^a` is a
`Y_étale`-derivation by `AlgebraicGeometry.SmallEtale.etaleAssociatedDerivation`.  A derivation
is determined by its values, so the two factorization conditions are the same condition. -/
public theorem existsUnique_postcomp_etaleAssociatedDerivation
    (F : SheafOfModules.{u} (structureSheaf B X.obj X.property)) (D : EtaleDerivation B f F) :
    ∃! g : associatedRelativeDifferentials B X.property (schemeHom B f) ⟶ F,
      (etaleAssociatedDerivation B f).postcomp g.val = D := by
  have key : ∀ g : associatedRelativeDifferentials B X.property (schemeHom B f) ⟶ F,
      ((etaleAssociatedDerivation B f).postcomp g.val = D ↔
        (associatedDerivation B X.property (schemeHom B f)).postcomp g.val =
          ofEtaleDerivation B f D) := by
    exact fun g => ⟨fun h => derivation_ext_of_d_eq (PresheafOfModules.Derivation.congr_d h),
      fun h => derivation_ext_of_d_eq (PresheafOfModules.Derivation.congr_d h)⟩
  obtain ⟨g, hg, hu⟩ := existsUnique_postcomp_associatedDerivation B X.property (schemeHom B f)
    (ofEtaleDerivation B f D)
    (d_pullbackSection_eq_zero B f D (fun V s => PresheafOfModules.Derivation'.d_app D s))
  exact ⟨g, (key g).2 hg, fun g' hg' => hu g' ((key g').1 hg')⟩

/-- `(Ω_{X/Y})^a` corepresents the functor of `Y_étale`-derivations, in the form
`CategoryTheory.Functor.CorepresentableBy`. -/
public noncomputable def associatedRelativeDifferentialsCorepresentableBy :
    (etaleDerivationsFunctor B f).CorepresentableBy
      (associatedRelativeDifferentials B X.property (schemeHom B f)) := by
  refine { homEquiv := ?_, homEquiv_comp := ?_ }
  · intro F
    refine ⟨fun g => (etaleAssociatedDerivation B f).postcomp g.val,
      fun D => Classical.choose (existsUnique_postcomp_etaleAssociatedDerivation B f F D),
      ?_, ?_⟩
    · intro g
      exact ((Classical.choose_spec (existsUnique_postcomp_etaleAssociatedDerivation B f F
        ((etaleAssociatedDerivation B f).postcomp g.val))).2 g rfl).symm
    · intro D
      exact (Classical.choose_spec
        (existsUnique_postcomp_etaleAssociatedDerivation B f F D)).1
  · intro F G g h
    change (etaleAssociatedDerivation B f).postcomp (h.val ≫ g.val) =
      ((etaleAssociatedDerivation B f).postcomp h.val).postcomp g.val
    ext V x
    rfl

/-- **Stacks 04CS.**  The canonical isomorphism `(Ω_{X/Y})^a ≅ Ω_{X_étale/Y_étale}`: both sides
corepresent the functor of `Y_étale`-derivations of `𝒪_{X_étale}`, the left one by
`AlgebraicGeometry.SmallEtale.existsUnique_postcomp_etaleAssociatedDerivation` and the right one
by `AlgebraicGeometry.SmallEtale.universalDerivation_isUniversal`. -/
@[stacks 04CS "the canonical isomorphism `(Ω_{X/Y})^a ≅ Ω_{X_étale/Y_étale}`"]
public noncomputable def differentialsIso :
    associatedRelativeDifferentials B X.property (schemeHom B f) ≅ sheafOfDifferentials B f :=
  SheafOfModules.corepresentableByIso (associatedRelativeDifferentialsCorepresentableBy B f)
    (sheafOfDifferentialsCorepresentableBy B f)

/-- **Stacks 04CS**, compatibility with the universal derivations: the canonical isomorphism
carries `d^a` to the universal `Y_étale`-derivation `d_{X_étale/Y_étale}`. -/
@[stacks 04CS "compatibility of the canonical isomorphism with the universal derivations"]
public theorem postcomp_differentialsIso_hom :
    (etaleAssociatedDerivation B f).postcomp (differentialsIso B f).hom.val =
      universalDerivation B f := by
  refine Eq.trans
    ((associatedRelativeDifferentialsCorepresentableBy B f).homEquiv.apply_symm_apply
      ((sheafOfDifferentialsCorepresentableBy B f).homEquiv
        (𝟙 (sheafOfDifferentials B f)))) ?_
  exact derivation_ext_of_d_eq fun _ => rfl

/-! ### The isomorphism is the comparison map `c''` of the source's proof -/

/-- The universal `Y_étale`-derivation annihilates every function pulled back from an open of
`Y`, so it is an admissible input to
`AlgebraicGeometry.SmallEtale.differentialsComparison`. -/
public theorem universalDerivation_pullbackSection_eq_zero (W : Y.obj.Opens) (b : Γ(Y.obj, W)) :
    (ofEtaleDerivation B f (universalDerivation B f)).d
        (pullbackSection B X.property (schemeHom B f) W b) = 0 :=
  d_pullbackSection_eq_zero B f (universalDerivation B f)
    (fun _ s => PresheafOfModules.Derivation'.d_app (universalDerivation B f) s) W b

/-- **The comparison map `c'' : (Ω_{X/Y})^a ⟶ Ω_{X_étale/Y_étale}` of the source's proof**:
`AlgebraicGeometry.SmallEtale.differentialsComparison` at the universal `Y_étale`-derivation of
`Ω_{X_étale/Y_étale}`. -/
public noncomputable abbrev universalDifferentialsComparison :
    associatedRelativeDifferentials B X.property (schemeHom B f) ⟶ sheafOfDifferentials B f :=
  differentialsComparison B X.property (schemeHom B f)
    (ofEtaleDerivation B f (universalDerivation B f))
    (universalDerivation_pullbackSection_eq_zero B f)

/-- **The canonical isomorphism of Stacks 04CS is the comparison map `c''` of the source's
proof.**  Both carry `d^a` to the universal `Y_étale`-derivation, and by
`AlgebraicGeometry.SmallEtale.existsUnique_postcomp_associatedDerivation` only one morphism
does. -/
public theorem differentialsIso_hom_eq :
    (differentialsIso B f).hom = universalDifferentialsComparison B f := by
  refine (existsUnique_postcomp_associatedDerivation B X.property (schemeHom B f)
    (ofEtaleDerivation B f (universalDerivation B f))
    (universalDerivation_pullbackSection_eq_zero B f)).unique ?_ ?_
  · exact derivation_ext_of_d_eq
      (PresheafOfModules.Derivation.congr_d (postcomp_differentialsIso_hom B f))
  · exact associatedDerivation_postcomp_differentialsComparison B X.property (schemeHom B f)
      (ofEtaleDerivation B f (universalDerivation B f))
      (universalDerivation_pullbackSection_eq_zero B f)

/-- **Stacks 04CS, the invertibility clause.**  The comparison map
`c'' : (Ω_{X/Y})^a ⟶ 𝓕` of `AlgebraicGeometry.SmallEtale.differentialsComparison` is an
isomorphism at `𝓕 = Ω_{X_étale/Y_étale}` carrying its universal derivation.  This is the
statement the tag's "canonical isomorphism" amounts to for the map the source's proof
produces. -/
@[stacks 04CS "the comparison map `c''` is an isomorphism at `𝓕 = Ω_{X_étale/Y_étale}`"]
public theorem isIso_universalDifferentialsComparison :
    IsIso (universalDifferentialsComparison B f) := by
  rw [← differentialsIso_hom_eq B f]
  infer_instance

end AlgebraicGeometry.SmallEtale

end
