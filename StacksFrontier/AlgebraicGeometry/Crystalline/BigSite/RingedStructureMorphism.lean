module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomOfRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.InverseImageComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposRelocalizedMorphism
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.StructureMorphism
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.RingedTopos
public import StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp
public import StacksCore.Tactic.StacksAttribute

/-!
# The structure morphism of the big crystalline site, as a morphism of ringed topoi

[Stacks, Tag 07IE] states its square and triangles as a diagram of morphisms of *ringed* topoi.
`StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.StructureMorphism` builds the diagram of
topoi; this file equips every corner with its structure sheaf and every arrow with its
structure map.

The big Zariski topos `Sh((Sch/Z)_Zar)` is ringed by `𝒪 : T/Z ↦ Γ(T, 𝒪_T)`, and the big
crystalline topos `(X/S)_CRIS` by the inverse image `U_{X/S}⁻¹𝒪`, which is the sheaf
`(U, T, δ) ↦ Γ(U, 𝒪_U)` that [Stacks, Tag 07IN] writes `\underline{𝐆_a}`.  Every arrow of the
diagram is then a morphism of ringed topoi, and the composite
`(X/S)_CRIS ⟶ Sh((Sch/S)_Zar)` -- the structure morphism of the big crystalline site -- is one
too.

## Main definitions

* `AlgebraicGeometry.zariskiOverStructureSheaf` -- the structure sheaf of commutative rings
  `𝒪 : T/Z ↦ Γ(T, 𝒪_T)` of the big Zariski site `(Sch/Z)_Zar`, and
  `AlgebraicGeometry.zariskiOverRingedTopos` the big Zariski topos of `Z` as a ringed topos.
* `AlgebraicGeometry.zariskiOverRingedMorphism` -- the morphism of *ringed* big Zariski topoi
  `Sh((Sch/X)_Zar) ⟶ Sh((Sch/Y)_Zar)` induced by a morphism of schemes `X ⟶ Y`; its structure
  map is invertible, both sides being `T ↦ Γ(T, 𝒪_T)`.
* `Crystalline.GlobalCrystallineSituation.crystallineZariskiRingedTopos` -- the big crystalline
  topos ringed by `U_{X/S}⁻¹𝒪`, and
  `Crystalline.GlobalCrystallineSituation.zariskiComparisonRinged` the comparison
  `U_{X/S} : (X/S)_CRIS ⟶ Sh((Sch/X)_Zar)` as a morphism of ringed topoi, the left vertical
  arrow of the diagram of [Stacks, Tag 07IE].
* `Crystalline.GlobalCrystallineSituation.structureMorphismRinged` -- the structure morphism of
  the big crystalline site as a morphism of ringed topoi, [Stacks, Tag 07IE].
* `Crystalline.GlobalCrystallineSituation.closedFiberZariskiRingedTopos`,
  `Crystalline.GlobalCrystallineSituation.closedFiberZariskiComparisonRinged` and
  `Crystalline.GlobalCrystallineSituation.closedFiberRingedMorphism` -- the remaining corner
  `(S₀/S)_CRIS` and the remaining two arrows `U_{S₀/S}` and
  `f_CRIS : (X/S)_CRIS ⟶ (S₀/S)_CRIS` of the diagram, as ringed topoi, and
  `Crystalline.GlobalCrystallineSituation.closedFiberStructureMorphismRinged` the structure
  morphism read along the upper route.
* `Crystalline.GlobalCrystallineSituation.comparisonSquareRinged`,
  `Crystalline.GlobalCrystallineSituation.zariskiStructureTriangleRinged` and
  `Crystalline.GlobalCrystallineSituation.closedFiberStructureTriangleRinged` -- the square, the
  big Zariski triangle and the resulting identification of the two routes
  `(X/S)_CRIS ⟶ Sh((Sch/S)_Zar)`, each as an `AlgebraicGeometry.RingedToposHom.TwoIso`: this is
  the commutativity of the diagram of [Stacks, Tag 07IE] at the ringed level.
* `AlgebraicGeometry.RingedToposHom.TwoIso.ofPushforwardIso` and `.ofPushforwardIsoCommRing` --
  a 2-isomorphism of morphisms of ringed topoi from a *prescribed* isomorphism of the direct
  images, with the compatibility of the two structure maps read on its mate, respectively read
  on sheaves of commutative rings.  The companion construction from an isomorphism of the
  inverse images is the existing
  `AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso`.

## Main results

* `AlgebraicGeometry.isIso_zariskiOverRingedMorphism_fSharpInverseImage` -- the structure map of
  a big Zariski arrow of the diagram is invertible: both structure sheaves are
  `T ↦ Γ(T, 𝒪_T)` and the arrow only changes the structure morphism of `T`.
* `Crystalline.GlobalCrystallineSituation.zariskiComparisonRinged_fSharpInverseImage` -- the
  structure map of the ringed comparison `U_{X/S}` is the identity in inverse-image form.
* `Crystalline.GlobalCrystallineSituation.isIso_closedFiberRingedMorphism_fSharpInverseImage` --
  the structure map of the ringed `f_CRIS` is invertible, being the identification of the two
  routes from `(X/S)_CRIS` to the big Zariski topos of `S₀`.
* `Crystalline.GlobalCrystallineSituation.structureMorphismRinged_toToposHom` and
  `Crystalline.GlobalCrystallineSituation.closedFiberStructureMorphismRinged_toToposHom` -- the
  underlying morphisms of topoi of the two ringed structure morphisms are the lower and upper
  routes of the diagram, which
  `Crystalline.GlobalCrystallineSituation.structureTriangle` and
  `Crystalline.GlobalCrystallineSituation.closedFiberStructureTriangle` identify with
  `Crystalline.GlobalCrystallineSituation.structureMorphism`.

* `Crystalline.GlobalCrystallineSituation.comparisonSquareRingedPushforward` -- the underlying
  2-isomorphism of topoi of the ringed square *is*
  `Crystalline.GlobalCrystallineSituation.comparisonSquare`, so the ringed square refines the
  square of topoi rather than replacing it.

## Implementation notes

**The structure sheaves.**  At the point where [Stacks, Tag 07IE] is stated no sheaf of rings on
a crystalline site has been introduced: the structure sheaf `𝒪_{X/S} : (U, T, δ) ↦ Γ(T, 𝒪_T)`
and its quotient `\underline{𝐆_a} : (U, T, δ) ↦ Γ(U, 𝒪_U)` appear only in [Stacks, Tag 07IN],
two sections later.  Of the two it is `\underline{𝐆_a}` for which the diagram is a diagram of
*ringed* topoi, and that is what is used here: the inverse image of a morphism of topoi attached
to a cocontinuous functor is restriction along that functor, so `U_{X/S}⁻¹𝒪` is
`(U, T, δ) ↦ Γ(U, 𝒪_U)` and the structure map of `U_{X/S}` is the unit of the adjunction, with
inverse-image form the identity.  For `𝒪_{X/S}` instead, the canonical map between the two
candidates runs `𝒪_{X/S} ⟶ \underline{𝐆_a} = U_{X/S}⁻¹𝒪` -- the restriction
`Γ(T, 𝒪_T) → Γ(U, 𝒪_U)` along the thickening -- which is the direction *opposite* to the
`U_{X/S}⁻¹𝒪 ⟶ 𝒪_{X/S}` that a morphism of ringed topoi
`((X/S)_CRIS, 𝒪_{X/S}) ⟶ (Sh((Sch/X)_Zar), 𝒪)` would require.  So the vertical arrows of the
diagram are not morphisms of ringed topoi for `𝒪_{X/S}`, and reading [Stacks, Tag 07IE] with
`\underline{𝐆_a}` is not a weakening but the only reading under which its own assertion holds.
`Crystalline.GlobalCrystallineSituation.crystallineStructureSheaf` -- the sheaf `𝒪_{X/S}` of
[Stacks, Tag 07IX] -- is therefore not the structure sheaf used here.

**The commutativity of the diagram.**  A diagram of ringed topoi commutes when its two
composites are 2-isomorphic in the sense of
`AlgebraicGeometry.RingedToposHom.TwoIso`, which asks for an isomorphism `e : f_* ≅ g_*` of the
direct images *and* for the equation `forgetFSharp f ≫ e.hom.app _ = forgetFSharp g` of the two
structure maps.  That equation is a computation with the adjunction mates of
`CategoryTheory.Adjunction.leftAdjointUniq` and `.rightAdjointUniq`, and the general
`AlgebraicGeometry.RingedToposHom.TwoIso.of...` constructions of the first section of this file
carry it out once and for all: a 2-morphism of topoi is compatible with the structure maps
exactly when its mate carries the inverse-image form of one to the inverse-image form of the
other, because the two forms of a structure map are adjunct
(`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv`).  For the square of the
remark the mate of `Crystalline.GlobalCrystallineSituation.comparisonSquare` is on the nose
`Crystalline.GlobalCrystallineSituation.comparisonSquareInverseImage`, which is the isomorphism
out of which the structure map of the ringed `f_CRIS` was built, so the equation holds for the
canonical `e`.  For the big Zariski triangle the comparison is built on the inverse-image side,
where all three inverse images are restriction along `Over.map`, and the isomorphism of direct
images is its conjugate.

**Universes.**  `AlgebraicGeometry.RingedTopos.Topos` is `Sheaf J (Type w)` for `w` the universe
of the sections of the structure sheaf, and the topoi of
`StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.StructureMorphism` are sheaves of
`Type (u + 1)` on sites whose objects are a `Type (u + 1)`: that is forced, because the
right Kan extension computing a pushforward is a limit over a comma category of that size.  The
sections `Γ(T, 𝒪_T)` of a `Scheme.{u}` are a `Type u`, so the structure sheaves here are the
universe lifts `CommRingCat.uliftFunctor` of the sheaves of sections.

**The sheaf condition for `𝒪` on the big Zariski site.**  It is inherited from the fpqc
topology, where `Stacks.Sites.isSheaf_fpqcOver_globalSections` has it: the Zariski topology is
coarser, `AlgebraicGeometry.zariskiTopologyOver_le_fpqcTopologyOver`.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 07ID](https://stacks.math.columbia.edu/tag/07ID)
* [Stacks Project, Tag 07IE](https://stacks.math.columbia.edu/tag/07IE)
* [Stacks Project, Tag 07IN](https://stacks.math.columbia.edu/tag/07IN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.RingedToposHom

universe v₁ u₁ w₁ v₂ u₂ w₂

variable {A : RingedTopos.{v₁, u₁, w₁}} {B : RingedTopos.{v₂, u₂, w₂}}
  [A.J.HasSheafCompose (forget RingCat.{w₁})]
  [B.J.HasSheafCompose (forget RingCat.{w₂})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]

/-- **The compatibility equation of a 2-morphism, read through the adjunctions.**  Both
structure maps are adjuncts, so the equation `forgetFSharp f ≫ t = forgetFSharp g` of
`AlgebraicGeometry.RingedToposHom.TwoIso` may be checked on the adjuncts. -/
theorem commutes_of_homEquiv (f g : RingedToposHom A B)
    (e : f.toToposHom.pushforward ≅ g.toToposHom.pushforward)
    (hkey : (f.toToposHom.adj.homEquiv (B.forgetRing.obj B.O) (A.forgetRing.obj A.O))
          (A.forgetRing.map f.fSharpInverseImage) ≫ e.hom.app (A.forgetRing.obj A.O) =
        (g.toToposHom.adj.homEquiv (B.forgetRing.obj B.O) (A.forgetRing.obj A.O))
          (A.forgetRing.map g.fSharpInverseImage)) :
    forgetFSharp f ≫ e.hom.app (A.forgetRing.obj A.O) = forgetFSharp g :=
  (congrArg (fun m ↦ m ≫ e.hom.app (A.forgetRing.obj A.O))
      (forgetFSharp_eq_homEquiv f)).trans
    (hkey.trans (forgetFSharp_eq_homEquiv g).symm)

/-- **The mate of an isomorphism of direct images.**  The isomorphism `g⁻¹ ≅ f⁻¹` of inverse
images determined by an isomorphism `f_* ≅ g_*` of direct images. -/
noncomputable def inverseImageMate (f g : RingedToposHom A B)
    (e : f.toToposHom.pushforward ≅ g.toToposHom.pushforward) :
    g.toToposHom.inverseImage ≅ f.toToposHom.inverseImage :=
  Adjunction.leftAdjointUniq (g.toToposHom.adj.ofNatIsoRight e.symm) f.toToposHom.adj

/-- **The defining property of the mate**, written on units: the unit of `f` followed by the
isomorphism of direct images is the unit of `g` followed by the direct image of the mate. -/
theorem unit_comp_inverseImageMate (f g : RingedToposHom A B)
    (e : f.toToposHom.pushforward ≅ g.toToposHom.pushforward) (W : B.Topos) :
    f.toToposHom.adj.unit.app W ≫ e.hom.app (f.toToposHom.inverseImage.obj W) =
      g.toToposHom.adj.unit.app W ≫
        g.toToposHom.pushforward.map ((inverseImageMate f g e).hom.app W) := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (g.toToposHom.adj.ofNatIsoRight e.symm) f.toToposHom.adj W
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit] at h
  rw [← h, inverseImageMate, Category.assoc, Iso.symm_hom, Iso.inv_hom_id_app,
    Category.comp_id]

/-- **The mate turns the adjunct under `f` into the adjunct under `g`.** -/
theorem homEquiv_comp_pushforwardIso (f g : RingedToposHom A B)
    (e : f.toToposHom.pushforward ≅ g.toToposHom.pushforward) (Y : A.Topos)
    (k : f.toToposHom.inverseImage.obj (B.forgetRing.obj B.O) ⟶ Y) :
    (f.toToposHom.adj.homEquiv _ Y) k ≫ e.hom.app Y =
      (g.toToposHom.adj.homEquiv _ Y)
        ((inverseImageMate f g e).hom.app (B.forgetRing.obj B.O) ≫ k) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc,
    e.hom.naturality k, ← Category.assoc, unit_comp_inverseImageMate f g e,
    Category.assoc, ← Functor.map_comp]

/-- **A 2-isomorphism of morphisms of ringed topoi with a prescribed isomorphism of direct
images.**  The isomorphism `f_* ≅ g_*` is a 2-isomorphism of ringed topoi as soon as its mate
carries the inverse-image form of the structure map of `f` to that of `g`. -/
noncomputable def TwoIso.ofPushforwardIso {f g : RingedToposHom A B}
    (e : f.toToposHom.pushforward ≅ g.toToposHom.pushforward)
    (h : (inverseImageMate f g e).hom.app (B.forgetRing.obj B.O) ≫
        A.forgetRing.map f.fSharpInverseImage = A.forgetRing.map g.fSharpInverseImage) :
    TwoIso f g where
  e := e
  commutes :=
    commutes_of_homEquiv f g e
      ((homEquiv_comp_pushforwardIso f g e _ _).trans
        (congrArg (g.toToposHom.adj.homEquiv (B.forgetRing.obj B.O)
          (A.forgetRing.obj A.O)) h))

/-- **The two transports of an inverse image of sheaves of commutative rings along an
isomorphism of inverse-image functors agree.**  Both are the identity on sections, read as a ring
homomorphism through `CategoryTheory.Sheaf.ringObjHom`. -/
theorem pullbackCommRingSheafCongr_hom_eq
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) {K : GrothendieckTopology D}
    [J.HasSheafCompose (forget RingCat.{w₁})]
    [J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
    [K.HasSheafCompose (forget RingCat.{w₂})]
    [K.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
    {Φ Ψ : Sheaf K (Type w₂) ⥤ Sheaf J (Type w₁)}
    [Limits.PreservesFiniteProducts Φ] [Limits.PreservesFiniteProducts Ψ]
    (e : Φ ≅ Ψ) (O : Sheaf K CommRingCat.{w₂}) :
    (Stacks.Sheaves.ToposPullback.pullbackCommRingSheafCongr J e O).hom =
      (Stacks.Sheaves.ToposPullback.pullbackCommRingSheafIsoOfNatIso J e O).hom :=
  rfl

/-- **The mate of an isomorphism of direct images, on sheaves of commutative rings.** -/
noncomputable def inverseImageCommRingMate (f g : RingedToposHom A B)
    (e : f.toToposHom.pushforward ≅ g.toToposHom.pushforward) :
    inverseImageCommRingFunctor g.toToposHom ≅ inverseImageCommRingFunctor f.toToposHom :=
  Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorIsoOfNatIso A.J
    (inverseImageMate f g e)

/-- On underlying sheaves of sets the ring-level mate is the mate. -/
theorem forgetRing_map_inverseImageCommRingMate (f g : RingedToposHom A B)
    (e : f.toToposHom.pushforward ≅ g.toToposHom.pushforward) :
    A.forgetRing.map ((inverseImageCommRingMate f g e).hom.app B.O) =
      (inverseImageMate f g e).hom.app (B.forgetRing.obj B.O) :=
  rfl

/-- **`AlgebraicGeometry.RingedToposHom.TwoIso.ofPushforwardIso` with its hypothesis read on
sheaves of commutative rings**, which is the level at which the two structure maps live. -/
noncomputable def TwoIso.ofPushforwardIsoCommRing {f g : RingedToposHom A B}
    (e : f.toToposHom.pushforward ≅ g.toToposHom.pushforward)
    (h : (inverseImageCommRingMate f g e).hom.app B.O ≫ f.fSharpInverseImage =
      g.fSharpInverseImage) :
    TwoIso f g :=
  TwoIso.ofPushforwardIso e
    ((congrArg (fun m ↦ m ≫ A.forgetRing.map f.fSharpInverseImage)
        (forgetRing_map_inverseImageCommRingMate f g e).symm).trans
      ((A.forgetRing.map_comp _ _).symm.trans (congrArg A.forgetRing.map h)))

section CompInverseImage

universe v₃ u₃

variable {A' : RingedTopos.{v₁, u₁, w₁}} {B' : RingedTopos.{v₂, u₂, w₁}}
  {C' : RingedTopos.{v₃, u₃, w₁}}
  [A'.J.HasSheafCompose (forget RingCat.{w₁})]
  [B'.J.HasSheafCompose (forget RingCat.{w₁})]
  [C'.J.HasSheafCompose (forget RingCat.{w₁})]
  [A'.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [C'.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]

/-- **The inverse-image form of the structure map of a composite of morphisms of ringed topoi**
is `AlgebraicGeometry.RingedToposHom.compFSharpInverseImage`.  The two agree because they do on
underlying sheaves of sets, where `AlgebraicGeometry.RingedToposHom.comp_fSharpInverseImage_forget`
and `AlgebraicGeometry.RingedToposHom.forget_map_compFSharpInverseImage` compute them, and
forgetting the ring operations of a sheaf of commutative rings is faithful. -/
theorem comp_fSharpInverseImage_eq (F : RingedToposHom B' C') (G : RingedToposHom A' B') :
    (F.comp G).fSharpInverseImage = compFSharpInverseImage F G :=
  A'.forgetRing.map_injective
    ((comp_fSharpInverseImage_forget F G).trans
      (forget_map_compFSharpInverseImage F G).symm)

end CompInverseImage

end AlgebraicGeometry.RingedToposHom


namespace AlgebraicGeometry

/-! ## The structure sheaf of the big Zariski site -/

/-- **The Zariski topology on a slice of schemes is coarser than the fpqc topology.**  A sieve
covers for the sliced topology exactly when its image sieve covers, and a Zariski covering sieve
of schemes is an fpqc covering sieve. -/
theorem zariskiTopologyOver_le_fpqcTopologyOver (Z : Scheme.{u}) :
    Scheme.zariskiTopology.over Z ≤ Scheme.fpqcTopology.over Z :=
  fun _ _ hR ↦ Scheme.zariskiTopology_le_fpqcTopology _ hR

/-- **The structure presheaf of commutative rings of the big Zariski site `(Sch/Z)_Zar`:** a
scheme `T` over `Z` is sent to the universe lift of the ring `Γ(T, 𝒪_T)` of its global
sections. -/
noncomputable def zariskiOverStructurePresheaf (Z : Scheme.{u}) :
    (Over Z)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (Over.forget Z).op ⋙ Scheme.Γ ⋙ CommRingCat.uliftFunctor.{u + 1, u}

/-- **The structure presheaf of the big Zariski site is a sheaf.**  Its underlying presheaf of
types is the universe lift of the presheaf of global sections, which is a sheaf for the fpqc
topology and hence for the coarser Zariski topology. -/
theorem isSheaf_zariskiOverStructurePresheaf (Z : Scheme.{u}) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over Z) (zariskiOverStructurePresheaf Z) := by
  refine CategoryTheory.Presheaf.isSheaf_of_isSheaf_forget_commRingCat _ _ ?_
  have h0 : Presieve.IsSheaf (Scheme.zariskiTopology.over Z)
      (Stacks.Sites.globalSectionsOver Z) :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).mp
      ((Stacks.Sites.isSheaf_fpqcOver_globalSections Z).of_le
        (zariskiTopologyOver_le_fpqcTopologyOver Z))
  have e : zariskiOverStructurePresheaf Z ⋙ forget CommRingCat.{u + 1} ≅
      Stacks.Sites.globalSectionsOver Z ⋙ CategoryTheory.uliftFunctor.{u + 1, u} :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  refine Presieve.isSheaf_iso _ e.symm ?_
  rw [Presieve.isSheaf_comp_uliftFunctor_iff]
  exact h0

/-- **The structure sheaf `𝒪` of the big Zariski site `(Sch/Z)_Zar`,** the sheaf of commutative
rings sending a scheme `T` over `Z` to `Γ(T, 𝒪_T)`. -/
@[stacks 07IE "the structure sheaf of the big Zariski topoi of the diagram"]
noncomputable def zariskiOverStructureSheaf (Z : Scheme.{u}) :
    Sheaf (Scheme.zariskiTopology.over Z) CommRingCat.{u + 1} :=
  ⟨zariskiOverStructurePresheaf Z, isSheaf_zariskiOverStructurePresheaf Z⟩

@[simp]
theorem zariskiOverStructureSheaf_val (Z : Scheme.{u}) :
    (zariskiOverStructureSheaf Z).obj = zariskiOverStructurePresheaf Z := rfl

/-- **The big Zariski topos of a scheme as a ringed topos,** [Stacks, Tag 07IE]: the site
`(Sch/Z)_Zar` together with its structure sheaf `T ↦ Γ(T, 𝒪_T)`. -/
@[stacks 07IE "the big Zariski topoi of the diagram, as ringed topoi"]
noncomputable def zariskiOverRingedTopos (Z : Scheme.{u}) : RingedTopos.{u, u + 1, u + 1} where
  C := Over Z
  J := Scheme.zariskiTopology.over Z
  O := zariskiOverStructureSheaf Z

@[simp]
theorem zariskiOverRingedTopos_J (Z : Scheme.{u}) :
    (zariskiOverRingedTopos Z).J = Scheme.zariskiTopology.over Z := rfl

@[simp]
theorem zariskiOverRingedTopos_O (Z : Scheme.{u}) :
    (zariskiOverRingedTopos Z).O = zariskiOverStructureSheaf Z := rfl

/-- **The underlying topos of the big Zariski ringed topos is the big Zariski topos.**  The two
spellings agree, so a morphism of topoi built in
`StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.StructureMorphism` is a morphism between the
underlying topoi of these ringed topoi. -/
theorem zariskiOverRingedTopos_topos (Z : Scheme.{u}) :
    (zariskiOverRingedTopos Z).Topos =
      Sheaf (Scheme.zariskiTopology.over Z) (Type (u + 1)) := rfl

/-! ## The big Zariski arrows as morphisms of ringed topoi -/

section ZariskiOver

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Restriction along `Over.map f` preserves finite products.**  Limits of sheaves are computed
pointwise in presheaves, where restriction along a functor is computed pointwise. -/
instance preservesFiniteProducts_overMap_sheafPushforwardContinuous :
    PreservesFiniteProducts ((Over.map f).sheafPushforwardContinuous (Type (u + 1))
      (Scheme.zariskiTopology.over X) (Scheme.zariskiTopology.over Y)) :=
  inferInstance

/-- **The inverse image of the morphism of big Zariski topoi is restriction along `Over.map f`.**
Both are left adjoint to the sheaf pushforward along `Over.map f`, which exists because
`Over.map f` is continuous as well as cocontinuous. -/
noncomputable def zariskiOverInverseImageIso :
    (zariskiOverMorphism f).inverseImage ≅
      (Over.map f).sheafPushforwardContinuous (Type (u + 1))
        (Scheme.zariskiTopology.over X) (Scheme.zariskiTopology.over Y) :=
  (zariskiOverMorphism f).adj.leftAdjointUniq
    ((Over.map f).sheafAdjunctionCocontinuous (Type (u + 1))
      (Scheme.zariskiTopology.over X) (Scheme.zariskiTopology.over Y))

/-- **The structure sheaf of the big Zariski site of `X` is the restriction of that of `Y`.**
Both send a scheme `T` to `Γ(T, 𝒪_T)`: `Over.map f` leaves the scheme untouched and only changes
the structure morphism. -/
theorem overMap_sheafPushforwardContinuous_obj_zariskiOverStructureSheaf :
    ((Over.map f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (Scheme.zariskiTopology.over X) (Scheme.zariskiTopology.over Y)).obj
      (zariskiOverStructureSheaf Y) = zariskiOverStructureSheaf X := rfl

/-- **The inverse image of the big Zariski structure sheaf along `f_big` is the big Zariski
structure sheaf.**  The inverse image is restriction along `Over.map f`, and restriction leaves
`T ↦ Γ(T, 𝒪_T)` untouched. -/
noncomputable def zariskiOverStructureInverseImageIso :
    (inverseImageCommRingFunctor (zariskiOverMorphism f)).obj (zariskiOverStructureSheaf Y) ≅
      zariskiOverStructureSheaf X :=
  inverseImageCommRingRestrictionIso (Scheme.zariskiTopology.over X)
    (Scheme.zariskiTopology.over Y) (Over.map f) (zariskiOverMorphism f)
    (zariskiOverInverseImageIso f) (zariskiOverStructureSheaf Y)

/-- **Stacks Project, Tag 07IE.**  The morphism of *ringed* big Zariski topoi
`Sh((Sch/X)_Zar) ⟶ Sh((Sch/Y)_Zar)` induced by a morphism of schemes `X ⟶ Y`: the underlying
morphism of topoi is `AlgebraicGeometry.zariskiOverMorphism`, and the structure map is the
adjunct of the identification of the inverse image of `T ↦ Γ(T, 𝒪_T)` with itself.  These are
the bottom and diagonal arrows `f_big` and `Sh((Sch/S₀)_Zar) ⟶ Sh((Sch/S)_Zar)` of the diagram
of the remark. -/
@[stacks 07IE "the big Zariski arrows of the diagram, as ringed topoi"]
noncomputable def zariskiOverRingedMorphism :
    RingedToposHom (zariskiOverRingedTopos X) (zariskiOverRingedTopos Y) :=
  RingedToposHom.ofInverseImageIso (X := zariskiOverRingedTopos X)
    (Y := zariskiOverRingedTopos Y) (zariskiOverMorphism f)
    (zariskiOverStructureInverseImageIso f)

@[simp]
theorem zariskiOverRingedMorphism_toToposHom :
    (zariskiOverRingedMorphism f).toToposHom = zariskiOverMorphism f := rfl

/-- **The structure map of the ringed big Zariski morphism is invertible.**  In inverse-image
form it is the identification of `T ↦ Γ(T, 𝒪_T)` with itself. -/
theorem isIso_zariskiOverRingedMorphism_fSharpInverseImage :
    IsIso (zariskiOverRingedMorphism f).fSharpInverseImage :=
  RingedToposHom.isIso_fSharpInverseImage_ofInverseImageIso (X := zariskiOverRingedTopos X)
    (Y := zariskiOverRingedTopos Y) (zariskiOverMorphism f)
    (zariskiOverStructureInverseImageIso f)

end ZariskiOver

/-! ## The big Zariski triangle of the diagram, as ringed topoi -/

section ZariskiOverComp

variable {X Y Z : Scheme.{u}}

/-- **The structure map of a ringed big Zariski arrow, in inverse-image form**, is the
identification of the inverse image of `T ↦ Γ(T, 𝒪_T)` with itself. -/
theorem zariskiOverRingedMorphism_fSharpInverseImage (f : X ⟶ Y) :
    (zariskiOverRingedMorphism f).fSharpInverseImage =
      (zariskiOverStructureInverseImageIso f).hom :=
  RingedToposHom.ofInverseImageIso_fSharpInverseImage (X := zariskiOverRingedTopos X)
    (Y := zariskiOverRingedTopos Y) (zariskiOverMorphism f)
    (zariskiOverStructureInverseImageIso f)

/-- **The same, on underlying sheaves of sets**, where it is the comparison of the inverse image
with restriction along `Over.map f`. -/
theorem zariskiOverRingedMorphism_fSharpInverseImage_forget (f : X ⟶ Y) :
    (zariskiOverRingedTopos X).forgetRing.map
        (zariskiOverRingedMorphism f).fSharpInverseImage =
      (zariskiOverInverseImageIso f).hom.app
        ((sheafCompose (Scheme.zariskiTopology.over Y)
          (forget CommRingCat.{u + 1})).obj (zariskiOverStructureSheaf Y)) :=
  (congrArg (zariskiOverRingedTopos X).forgetRing.map
      (zariskiOverRingedMorphism_fSharpInverseImage f)).trans
    (Stacks.Sheaves.ToposPullback.inverseImageCommRingRestrictionIso_hom_forget
      (Scheme.zariskiTopology.over X) (Scheme.zariskiTopology.over Y) (Over.map f)
      (zariskiOverMorphism f) (zariskiOverInverseImageIso f) (zariskiOverStructureSheaf Y))

/-- **The inverse images of the big Zariski arrows compose.**  Each of the three inverse images
is restriction along `Over.map`, and restriction along `Over.map (a ≫ b)` is restriction along
`Over.map b` followed by restriction along `Over.map a`. -/
noncomputable def zariskiOverInverseImageComp (a : X ⟶ Y) (b : Y ⟶ Z) :
    (zariskiOverMorphism (a ≫ b)).inverseImage ≅
      (zariskiOverMorphism b).inverseImage ⋙ (zariskiOverMorphism a).inverseImage :=
  zariskiOverInverseImageIso (a ≫ b) ≪≫
    (Functor.sheafPushforwardContinuousComp' (Over.mapComp a b).symm (Type (u + 1))
      (Scheme.zariskiTopology.over X) (Scheme.zariskiTopology.over Y)
      (Scheme.zariskiTopology.over Z)).symm ≪≫
    Functor.isoWhiskerRight (zariskiOverInverseImageIso b).symm
      ((Over.map a).sheafPushforwardContinuous (Type (u + 1))
        (Scheme.zariskiTopology.over X) (Scheme.zariskiTopology.over Y)) ≪≫
    Functor.isoWhiskerLeft (zariskiOverMorphism b).inverseImage
      (zariskiOverInverseImageIso a).symm

/-- **At the big Zariski structure sheaf the comparison of restrictions is the identity.**  Both
restrictions send `T ↦ Γ(T, 𝒪_T)` to itself, `Over.map` leaving the scheme untouched. -/
theorem restrictionComp_inv_app_zariskiOverStructureSheaf (a : X ⟶ Y) (b : Y ⟶ Z) :
    (Functor.sheafPushforwardContinuousComp' (Over.mapComp a b).symm (Type (u + 1))
        (Scheme.zariskiTopology.over X) (Scheme.zariskiTopology.over Y)
        (Scheme.zariskiTopology.over Z)).inv.app
      ((sheafCompose (Scheme.zariskiTopology.over Z)
        (forget CommRingCat.{u + 1})).obj (zariskiOverStructureSheaf Z)) =
      𝟙 (((Over.map b).sheafPushforwardContinuous (Type (u + 1))
        (Scheme.zariskiTopology.over Y) (Scheme.zariskiTopology.over Z) ⋙
          (Over.map a).sheafPushforwardContinuous (Type (u + 1))
            (Scheme.zariskiTopology.over X) (Scheme.zariskiTopology.over Y)).obj
        ((sheafCompose (Scheme.zariskiTopology.over Z)
          (forget CommRingCat.{u + 1})).obj (zariskiOverStructureSheaf Z))) := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun _ ↦ ?_)
  rfl

/-- **The composition of inverse images is compatible with the two structure maps.**  This is
the hypothesis of `AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso` for the big Zariski
triangle, read on underlying sheaves of sets. -/
theorem zariskiOverInverseImageComp_hom_app_comp (a : X ⟶ Y) (b : Y ⟶ Z) :
    (zariskiOverInverseImageComp a b).hom.app
        ((sheafCompose (Scheme.zariskiTopology.over Z)
          (forget CommRingCat.{u + 1})).obj (zariskiOverStructureSheaf Z)) ≫
      ((zariskiOverMorphism a).inverseImage.map
          ((zariskiOverInverseImageIso b).hom.app
            ((sheafCompose (Scheme.zariskiTopology.over Z)
              (forget CommRingCat.{u + 1})).obj (zariskiOverStructureSheaf Z))) ≫
        (zariskiOverInverseImageIso a).hom.app
          ((sheafCompose (Scheme.zariskiTopology.over Y)
            (forget CommRingCat.{u + 1})).obj (zariskiOverStructureSheaf Y))) =
      (zariskiOverInverseImageIso (a ≫ b)).hom.app
        ((sheafCompose (Scheme.zariskiTopology.over Z)
          (forget CommRingCat.{u + 1})).obj (zariskiOverStructureSheaf Z)) := by
  set OZ := (sheafCompose (Scheme.zariskiTopology.over Z)
    (forget CommRingCat.{u + 1})).obj (zariskiOverStructureSheaf Z)
  set Wa := (Over.map a).sheafPushforwardContinuous (Type (u + 1))
    (Scheme.zariskiTopology.over X) (Scheme.zariskiTopology.over Y)
  have h2 : (Wa.map ((zariskiOverInverseImageIso b).inv.app OZ) ≫
        (zariskiOverInverseImageIso a).inv.app
          ((zariskiOverMorphism b).inverseImage.obj OZ)) ≫
      ((zariskiOverMorphism a).inverseImage.map
          ((zariskiOverInverseImageIso b).hom.app OZ) ≫
        (zariskiOverInverseImageIso a).hom.app
          (((Over.map b).sheafPushforwardContinuous (Type (u + 1))
            (Scheme.zariskiTopology.over Y) (Scheme.zariskiTopology.over Z)).obj OZ)) =
      𝟙 (Wa.obj (((Over.map b).sheafPushforwardContinuous (Type (u + 1))
        (Scheme.zariskiTopology.over Y) (Scheme.zariskiTopology.over Z)).obj OZ)) := by
    rw [Category.assoc, ← Category.assoc ((zariskiOverInverseImageIso a).inv.app _),
      ← (zariskiOverInverseImageIso a).inv.naturality
        ((zariskiOverInverseImageIso b).hom.app OZ)]
    simp [← Functor.map_comp]
  simp only [zariskiOverInverseImageComp, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, restrictionComp_inv_app_zariskiOverStructureSheaf,
    Category.assoc]
  refine (congrArg (_ ≫ ·) ?_).trans (Category.comp_id _)
  erw [Category.id_comp]
  exact h2

/-- **Stacks Project, Tag 07IE.**  The morphisms of *ringed* big Zariski topoi compose: the
composite of the arrows along `a : X ⟶ Y` and `b : Y ⟶ Z` is 2-isomorphic, as a morphism of
ringed topoi, to the arrow along `a ≫ b`. -/
noncomputable def zariskiOverRingedMorphismComp (a : X ⟶ Y) (b : Y ⟶ Z) :
    RingedToposHom.TwoIso.{u, u + 1, u + 1, u, u + 1, u + 1}
      (RingedToposHom.comp (X := zariskiOverRingedTopos X)
        (Y := zariskiOverRingedTopos Y) (Z := zariskiOverRingedTopos Z)
        (zariskiOverRingedMorphism b) (zariskiOverRingedMorphism a))
      (zariskiOverRingedMorphism (a ≫ b)) :=
  RingedToposHom.TwoIso.ofInverseImageIso.{u, u + 1, u + 1, u, u + 1, u + 1}
    (zariskiOverInverseImageComp a b)
    (((congrArg (fun m ↦ (zariskiOverInverseImageComp a b).hom.app
          ((sheafCompose (Scheme.zariskiTopology.over Z)
            (forget CommRingCat.{u + 1})).obj (zariskiOverStructureSheaf Z)) ≫ m)
        ((RingedToposHom.comp_fSharpInverseImage_forget
            (zariskiOverRingedMorphism b) (zariskiOverRingedMorphism a)).trans
          ((congrArg (fun m ↦ (zariskiOverMorphism a).inverseImage.map m ≫
              (zariskiOverRingedTopos X).forgetRing.map
                (zariskiOverRingedMorphism a).fSharpInverseImage)
            (zariskiOverRingedMorphism_fSharpInverseImage_forget b)).trans
            (congrArg (fun m ↦ (zariskiOverMorphism a).inverseImage.map
                ((zariskiOverInverseImageIso b).hom.app
                  ((sheafCompose (Scheme.zariskiTopology.over Z)
                    (forget CommRingCat.{u + 1})).obj (zariskiOverStructureSheaf Z))) ≫ m)
              (zariskiOverRingedMorphism_fSharpInverseImage_forget a))))).trans
      (zariskiOverInverseImageComp_hom_app_comp a b)).trans
      (zariskiOverRingedMorphism_fSharpInverseImage_forget (a ≫ b)).symm)

end ZariskiOverComp


end AlgebraicGeometry

namespace Crystalline.GlobalCrystallineSituation

open Thickening

/-! ## The big crystalline topos as a ringed topos -/

/-- **Stacks Project, Tag 07IE.**  The big crystalline topos `(X/S)_CRIS` as a ringed topos: the
site `CRIS(X/S)` together with the inverse image `U_{X/S}⁻¹𝒪` of the structure sheaf of the big
Zariski site of `X`.  Since the inverse image of the morphism of topoi attached to a cocontinuous
functor is restriction along that functor, this structure sheaf is
`(U, T, δ) ↦ Γ(U, 𝒪_U)`, the sheaf `\underline{𝐆_a}` of [Stacks, Tag 07IN]. -/
@[stacks 07IE "the big crystalline topoi of the diagram, as ringed topoi"]
noncomputable abbrev crystallineZariskiRingedTopos (S : GlobalCrystallineSituation.{u}) :
    RingedTopos.{u, u + 1, u + 1} :=
  inverseImageRingedTopos (Thickening S) (topology S) (zariskiOverRingedTopos S.X)
    (zariskiComparison S)

/-- **Stacks Project, Tag 07IE.**  The comparison with the Zariski site
`U_{X/S} : (X/S)_CRIS ⟶ Sh((Sch/X)_Zar)` as a morphism of ringed topoi -- the left vertical arrow
of the diagram of the remark.  Its structure map is the unit of the adjunction between the
inverse image and the direct image of sheaves of commutative rings, whose inverse-image form is
the identity. -/
@[stacks 07IE "the crystalline-to-Zariski comparisons of the diagram, as ringed topoi",
  stacks 07ID "the comparison as a morphism of ringed topoi"]
noncomputable def zariskiComparisonRinged (S : GlobalCrystallineSituation.{u}) :
    RingedToposHom (crystallineZariskiRingedTopos S) (zariskiOverRingedTopos S.X) :=
  inverseImageRingedToposHom (Thickening S) (topology S) (zariskiOverRingedTopos S.X)
    (zariskiComparison S)

@[simp]
theorem zariskiComparisonRinged_toToposHom (S : GlobalCrystallineSituation.{u}) :
    (zariskiComparisonRinged S).toToposHom = zariskiComparison S := rfl

/-- **The structure map of the ringed comparison is the identity in inverse-image form.**  The
structure sheaf of `(X/S)_CRIS` *is* the inverse image of the big Zariski structure sheaf. -/
theorem zariskiComparisonRinged_fSharpInverseImage (S : GlobalCrystallineSituation.{u}) :
    (zariskiComparisonRinged S).fSharpInverseImage =
      𝟙 (crystallineZariskiRingedTopos S).O :=
  inverseImageRingedToposHom_fSharpInverseImage (Thickening S) (topology S)
    (zariskiOverRingedTopos S.X) (zariskiComparison S)

/-! ## The structure morphism as a morphism of ringed topoi -/

/-- **Stacks Project, Tag 07IE.**  The structure morphism of the big crystalline site
`(X/S)_CRIS ⟶ Sh((Sch/S)_Zar)` as a morphism of *ringed* topoi: the comparison `U_{X/S}`
followed by the big Zariski morphism along `X ⟶ S`.  This is the lower route through the diagram
of the remark, which is what defines the structure morphism whether or not `p` is locally
nilpotent on the closed fibre. -/
@[stacks 07IE "the structure morphism, as a morphism of ringed topoi"]
noncomputable def structureMorphismRinged (S : GlobalCrystallineSituation.{u}) :
    RingedToposHom (crystallineZariskiRingedTopos S) (zariskiOverRingedTopos S.S.scheme) :=
  RingedToposHom.comp (X := crystallineZariskiRingedTopos S)
    (Y := zariskiOverRingedTopos S.X) (Z := zariskiOverRingedTopos S.S.scheme)
    (zariskiOverRingedMorphism (sourceToBase S)) (zariskiComparisonRinged S)

@[simp]
theorem structureMorphismRinged_toToposHom (S : GlobalCrystallineSituation.{u}) :
    (structureMorphismRinged S).toToposHom =
      (zariskiOverMorphism (sourceToBase S)).comp (zariskiComparison S) := rfl

/-! ## The closed fibre: the top and right arrows of the diagram -/

section ClosedFiber

variable (S : GlobalCrystallineSituation.{u})
  (hp : ∀ x : DividedPowerScheme.closedFiber S.S,
    IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x))

/-- **Stacks Project, Tag 07IE.**  The crystalline topos `(S₀/S)_CRIS` of the closed fibre as a
ringed topos: the upper right corner of the diagram of the remark, available because `p` is
locally nilpotent on `S₀`. -/
@[stacks 07IE "the crystalline topos of the closed fibre, as a ringed topos"]
noncomputable abbrev closedFiberZariskiRingedTopos : RingedTopos.{u, u + 1, u + 1} :=
  crystallineZariskiRingedTopos (closedFiberSituation S hp)

/-- **Stacks Project, Tag 07IE.**  The comparison `U_{S₀/S} : (S₀/S)_CRIS ⟶ Sh((Sch/S₀)_Zar)` as
a morphism of ringed topoi: the right vertical arrow of the diagram. -/
@[stacks 07IE "the right vertical arrow of the diagram, as ringed topoi"]
noncomputable def closedFiberZariskiComparisonRinged :
    RingedToposHom (closedFiberZariskiRingedTopos S hp)
      (zariskiOverRingedTopos (DividedPowerScheme.closedFiber S.S)) :=
  zariskiComparisonRinged (closedFiberSituation S hp)

@[simp]
theorem closedFiberZariskiComparisonRinged_toToposHom :
    (closedFiberZariskiComparisonRinged S hp).toToposHom =
      zariskiComparison (closedFiberSituation S hp) := rfl

/-- **The two routes `(X/S)_CRIS ⟶ Sh((Sch/S₀)_Zar)` have isomorphic inverse images.**  The mate
of `Crystalline.GlobalCrystallineSituation.comparisonSquare` under the two adjunctions: a
left adjoint is determined by its right adjoint up to canonical isomorphism. -/
noncomputable def comparisonSquareInverseImage :
    ((zariskiComparison (closedFiberSituation S hp)).comp
        (closedFiberMorphism S hp)).inverseImage ≅
      ((zariskiOverMorphism S.toClosedFiber).comp (zariskiComparison S)).inverseImage :=
  Adjunction.leftAdjointUniq
    (((zariskiComparison (closedFiberSituation S hp)).comp
      (closedFiberMorphism S hp)).adj.ofNatIsoRight (comparisonSquare S hp).symm)
    ((zariskiOverMorphism S.toClosedFiber).comp (zariskiComparison S)).adj

/-- **The inverse image along `f_CRIS` of the structure sheaf of `(S₀/S)_CRIS` is the structure
sheaf of `(X/S)_CRIS`.**  Both are the inverse image of `T ↦ Γ(T, 𝒪_T)` along a route from
`(X/S)_CRIS` to the big Zariski topos of `S₀`, and the square of
`Crystalline.GlobalCrystallineSituation.comparisonSquare` identifies the two routes. -/
noncomputable def closedFiberStructureInverseImageIso :
    (inverseImageCommRingFunctor (closedFiberMorphism S hp)).obj
        (closedFiberZariskiRingedTopos S hp).O ≅
      (crystallineZariskiRingedTopos S).O :=
  (inverseImageCommRingComp (zariskiComparison (closedFiberSituation S hp))
        (closedFiberMorphism S hp)).app
      (zariskiOverStructureSheaf (DividedPowerScheme.closedFiber S.S)) ≪≫
    pullbackCommRingSheafCongr (topology S) (comparisonSquareInverseImage S hp)
      (zariskiOverStructureSheaf (DividedPowerScheme.closedFiber S.S)) ≪≫
    ((inverseImageCommRingComp (zariskiOverMorphism S.toClosedFiber)
        (zariskiComparison S)).app
      (zariskiOverStructureSheaf (DividedPowerScheme.closedFiber S.S))).symm ≪≫
    (inverseImageCommRingFunctor (zariskiComparison S)).mapIso
      (zariskiOverStructureInverseImageIso S.toClosedFiber)

/-- **Stacks Project, Tag 07IE.**  The top arrow `f_CRIS : (X/S)_CRIS ⟶ (S₀/S)_CRIS` of the
diagram as a morphism of ringed topoi, for `f : X ⟶ S₀` the structure morphism.  Its structure
map is invertible, being the identification of the two routes to the big Zariski topos of
`S₀`. -/
@[stacks 07IE "the top arrow of the diagram, as ringed topoi"]
noncomputable def closedFiberRingedMorphism :
    RingedToposHom (crystallineZariskiRingedTopos S) (closedFiberZariskiRingedTopos S hp) :=
  RingedToposHom.ofInverseImageIso (X := crystallineZariskiRingedTopos S)
    (Y := closedFiberZariskiRingedTopos S hp) (closedFiberMorphism S hp)
    (closedFiberStructureInverseImageIso S hp)

@[simp]
theorem closedFiberRingedMorphism_toToposHom :
    (closedFiberRingedMorphism S hp).toToposHom = closedFiberMorphism S hp := rfl

/-- **The structure map of the ringed top arrow is invertible.** -/
theorem isIso_closedFiberRingedMorphism_fSharpInverseImage :
    IsIso (closedFiberRingedMorphism S hp).fSharpInverseImage :=
  RingedToposHom.isIso_fSharpInverseImage_ofInverseImageIso
    (X := crystallineZariskiRingedTopos S) (Y := closedFiberZariskiRingedTopos S hp)
    (closedFiberMorphism S hp) (closedFiberStructureInverseImageIso S hp)

/-- **Stacks Project, Tag 07IE.**  The structure morphism of the big crystalline site read along
the upper route of the diagram: `f_CRIS`, then `U_{S₀/S}`, then the big Zariski morphism along
`S₀ ⟶ S`.  This is the composition the remark takes as the definition of the structure morphism
when `p` is locally nilpotent on the closed fibre. -/
@[stacks 07IE "the structure morphism through the closed fibre, as ringed topoi"]
noncomputable def closedFiberStructureMorphismRinged :
    RingedToposHom (crystallineZariskiRingedTopos S) (zariskiOverRingedTopos S.S.scheme) :=
  RingedToposHom.comp (X := crystallineZariskiRingedTopos S)
    (Y := closedFiberZariskiRingedTopos S hp) (Z := zariskiOverRingedTopos S.S.scheme)
    (RingedToposHom.comp (X := closedFiberZariskiRingedTopos S hp)
      (Y := zariskiOverRingedTopos (DividedPowerScheme.closedFiber S.S))
      (Z := zariskiOverRingedTopos S.S.scheme)
      (zariskiOverRingedMorphism (DividedPowerScheme.closedFiberι S.S))
      (closedFiberZariskiComparisonRinged S hp))
    (closedFiberRingedMorphism S hp)

@[simp]
theorem closedFiberStructureMorphismRinged_toToposHom :
    (closedFiberStructureMorphismRinged S hp).toToposHom =
      ((zariskiOverMorphism (DividedPowerScheme.closedFiberι S.S)).comp
          (zariskiComparison (closedFiberSituation S hp))).comp
        (closedFiberMorphism S hp) := rfl

/-! ### The commutativity of the diagram, at the ringed level -/

/-- The structure map of the ringed comparison of the closed fibre is the identity in
inverse-image form. -/
theorem closedFiberZariskiComparisonRinged_fSharpInverseImage :
    (closedFiberZariskiComparisonRinged S hp).fSharpInverseImage =
      𝟙 (crystallineZariskiRingedTopos (closedFiberSituation S hp)).O :=
  zariskiComparisonRinged_fSharpInverseImage (closedFiberSituation S hp)

/-- The structure map of the ringed top arrow, in inverse-image form. -/
theorem closedFiberRingedMorphism_fSharpInverseImage :
    (closedFiberRingedMorphism S hp).fSharpInverseImage =
      (closedFiberStructureInverseImageIso S hp).hom :=
  RingedToposHom.ofInverseImageIso_fSharpInverseImage
    (X := crystallineZariskiRingedTopos S) (Y := closedFiberZariskiRingedTopos S hp)
    (closedFiberMorphism S hp) (closedFiberStructureInverseImageIso S hp)

/-- The four factors of the identification of inverse images along the upper route, spelled
out. -/
theorem closedFiberStructureInverseImageIso_hom :
    (closedFiberStructureInverseImageIso S hp).hom =
      (inverseImageCommRingComp (zariskiComparison (closedFiberSituation S hp))
            (closedFiberMorphism S hp)).hom.app
          (zariskiOverStructureSheaf (DividedPowerScheme.closedFiber S.S)) ≫
        (pullbackCommRingSheafCongr (topology S) (comparisonSquareInverseImage S hp)
            (zariskiOverStructureSheaf (DividedPowerScheme.closedFiber S.S))).hom ≫
          (inverseImageCommRingComp (zariskiOverMorphism S.toClosedFiber)
              (zariskiComparison S)).inv.app
            (zariskiOverStructureSheaf (DividedPowerScheme.closedFiber S.S)) ≫
            (inverseImageCommRingFunctor (zariskiComparison S)).map
              (zariskiOverStructureInverseImageIso S.toClosedFiber).hom :=
  rfl

/-- **The topos-level square of [Stacks, Tag 07IE], at the spelling of its type carried by the
two composites of morphisms of ringed topoi.** -/
noncomputable def comparisonSquareRingedPushforward :
    (RingedToposHom.comp (X := crystallineZariskiRingedTopos S)
      (Y := zariskiOverRingedTopos S.X)
      (Z := zariskiOverRingedTopos (DividedPowerScheme.closedFiber S.S))
      (zariskiOverRingedMorphism S.toClosedFiber)
      (zariskiComparisonRinged S)).toToposHom.pushforward ≅
    (RingedToposHom.comp (X := crystallineZariskiRingedTopos S)
      (Y := closedFiberZariskiRingedTopos S hp)
      (Z := zariskiOverRingedTopos (DividedPowerScheme.closedFiber S.S))
      (closedFiberZariskiComparisonRinged S hp)
      (closedFiberRingedMorphism S hp)).toToposHom.pushforward :=
  comparisonSquare S hp

/-- **Stacks Project, Tag 07IE.**  The square of the diagram commutes as a diagram of *ringed*
topoi: `U_{S₀/S} ∘ f_CRIS` and `f_big ∘ U_{X/S}` are 2-isomorphic as morphisms of ringed topoi,
the underlying 2-isomorphism of topoi being
`Crystalline.GlobalCrystallineSituation.comparisonSquare`. -/
@[stacks 07IE "the square of the diagram, as ringed topoi"]
noncomputable def comparisonSquareRinged :
    RingedToposHom.TwoIso.{u, u + 1, u + 1, u, u + 1, u + 1}
      (RingedToposHom.comp (X := crystallineZariskiRingedTopos S)
        (Y := zariskiOverRingedTopos S.X)
        (Z := zariskiOverRingedTopos (DividedPowerScheme.closedFiber S.S))
        (zariskiOverRingedMorphism S.toClosedFiber) (zariskiComparisonRinged S))
      (RingedToposHom.comp (X := crystallineZariskiRingedTopos S)
        (Y := closedFiberZariskiRingedTopos S hp)
        (Z := zariskiOverRingedTopos (DividedPowerScheme.closedFiber S.S))
        (closedFiberZariskiComparisonRinged S hp) (closedFiberRingedMorphism S hp)) :=
  RingedToposHom.TwoIso.ofPushforwardIsoCommRing.{u, u + 1, u + 1, u, u + 1, u + 1}
    (comparisonSquareRingedPushforward S hp) (by
      have h1 : (inverseImageCommRingFunctor (closedFiberMorphism S hp)).map
          (closedFiberZariskiComparisonRinged S hp).fSharpInverseImage =
          𝟙 ((inverseImageCommRingFunctor (closedFiberMorphism S hp)).obj
            (crystallineZariskiRingedTopos (closedFiberSituation S hp)).O) :=
        (congrArg (inverseImageCommRingFunctor (closedFiberMorphism S hp)).map
          (closedFiberZariskiComparisonRinged_fSharpInverseImage S hp)).trans
          (CategoryTheory.Functor.map_id _ _)
      have hf : (RingedToposHom.comp (X := crystallineZariskiRingedTopos S)
            (Y := zariskiOverRingedTopos S.X)
            (Z := zariskiOverRingedTopos (DividedPowerScheme.closedFiber S.S))
            (zariskiOverRingedMorphism S.toClosedFiber)
            (zariskiComparisonRinged S)).fSharpInverseImage =
          (inverseImageCommRingComp (zariskiOverMorphism S.toClosedFiber)
                (zariskiComparison S)).inv.app
              (zariskiOverStructureSheaf (DividedPowerScheme.closedFiber S.S)) ≫
            (inverseImageCommRingFunctor (zariskiComparison S)).map
              (zariskiOverStructureInverseImageIso S.toClosedFiber).hom :=
        (RingedToposHom.comp_fSharpInverseImage_eq
            (zariskiOverRingedMorphism S.toClosedFiber) (zariskiComparisonRinged S)).trans
          (congrArg (fun m ↦ (inverseImageCommRingComp (zariskiOverMorphism S.toClosedFiber)
                (zariskiComparison S)).inv.app
              (zariskiOverStructureSheaf (DividedPowerScheme.closedFiber S.S)) ≫ m)
            (((congrArg (fun m ↦ (inverseImageCommRingFunctor (zariskiComparison S)).map m ≫
                    (zariskiComparisonRinged S).fSharpInverseImage)
                  (zariskiOverRingedMorphism_fSharpInverseImage S.toClosedFiber)).trans
                (congrArg (fun m ↦ (inverseImageCommRingFunctor (zariskiComparison S)).map
                    (zariskiOverStructureInverseImageIso S.toClosedFiber).hom ≫ m)
                  (zariskiComparisonRinged_fSharpInverseImage S))).trans
              (Category.comp_id _)))
      have hg : (RingedToposHom.comp (X := crystallineZariskiRingedTopos S)
            (Y := closedFiberZariskiRingedTopos S hp)
            (Z := zariskiOverRingedTopos (DividedPowerScheme.closedFiber S.S))
            (closedFiberZariskiComparisonRinged S hp)
            (closedFiberRingedMorphism S hp)).fSharpInverseImage =
          (pullbackCommRingSheafCongr (topology S) (comparisonSquareInverseImage S hp)
              (zariskiOverStructureSheaf (DividedPowerScheme.closedFiber S.S))).hom ≫
            (inverseImageCommRingComp (zariskiOverMorphism S.toClosedFiber)
                  (zariskiComparison S)).inv.app
                (zariskiOverStructureSheaf (DividedPowerScheme.closedFiber S.S)) ≫
              (inverseImageCommRingFunctor (zariskiComparison S)).map
                (zariskiOverStructureInverseImageIso S.toClosedFiber).hom :=
        (RingedToposHom.comp_fSharpInverseImage_eq
            (closedFiberZariskiComparisonRinged S hp)
            (closedFiberRingedMorphism S hp)).trans
          ((congrArg (fun m ↦ (inverseImageCommRingComp
                  (zariskiComparison (closedFiberSituation S hp))
                  (closedFiberMorphism S hp)).inv.app
                (zariskiOverStructureSheaf (DividedPowerScheme.closedFiber S.S)) ≫ m)
              (((congrArg (fun m ↦ (inverseImageCommRingFunctor
                      (closedFiberMorphism S hp)).map
                        (closedFiberZariskiComparisonRinged S hp).fSharpInverseImage ≫ m)
                    (closedFiberRingedMorphism_fSharpInverseImage S hp)).trans
                  ((congrArg (fun m ↦ m ≫
                        (closedFiberStructureInverseImageIso S hp).hom) h1).trans
                    (Category.id_comp _))).trans
                (closedFiberStructureInverseImageIso_hom S hp))).trans
            (Iso.inv_hom_id_app_assoc _ _ _))
      rw [hf, hg]
      rfl)

/-- **Stacks Project, Tag 07IE.**  The lower triangle of the diagram commutes as a diagram of
*ringed* topoi: the big Zariski morphisms along `X ⟶ S₀` and `S₀ ⟶ S` compose, as morphisms of
ringed topoi, to the one along `X ⟶ S`. -/
@[stacks 07IE "the big Zariski triangle of the diagram, as ringed topoi"]
noncomputable def zariskiStructureTriangleRinged :
    RingedToposHom.TwoIso.{u, u + 1, u + 1, u, u + 1, u + 1}
      (RingedToposHom.comp
        (X := zariskiOverRingedTopos S.X)
        (Y := zariskiOverRingedTopos (DividedPowerScheme.closedFiber S.S))
        (Z := zariskiOverRingedTopos S.S.scheme)
        (zariskiOverRingedMorphism (DividedPowerScheme.closedFiberι S.S))
        (zariskiOverRingedMorphism S.toClosedFiber))
      (zariskiOverRingedMorphism (sourceToBase S)) :=
  zariskiOverRingedMorphismComp S.toClosedFiber (DividedPowerScheme.closedFiberι S.S)

/-- **Stacks Project, Tag 07IE.**  The diagram of *ringed* topoi commutes: the structure
morphism of the big crystalline site read along the upper route -- `f_CRIS`, then `U_{S₀/S}`,
then the big Zariski morphism along `S₀ ⟶ S` -- is 2-isomorphic, as a morphism of ringed topoi,
to the one read along the lower route, which is
`Crystalline.GlobalCrystallineSituation.structureMorphismRinged`.  This is the assertion of the
remark, pasted out of the square and the big Zariski triangle. -/
@[stacks 07IE "the commutativity of the diagram of ringed topoi: the two routes from (X/S)_CRIS
  to the big Zariski topos of S agree"]
noncomputable def closedFiberStructureTriangleRinged :
    RingedToposHom.TwoIso.{u, u + 1, u + 1, u, u + 1, u + 1}
      (closedFiberStructureMorphismRinged S hp) (structureMorphismRinged S) :=
  ((RingedToposHom.TwoIso.associator (closedFiberRingedMorphism S hp)
          (closedFiberZariskiComparisonRinged S hp)
          (zariskiOverRingedMorphism
            (DividedPowerScheme.closedFiberι S.S))).symm.trans
      (RingedToposHom.TwoIso.whiskerRight (comparisonSquareRinged S hp).symm
        (zariskiOverRingedMorphism (DividedPowerScheme.closedFiberι S.S)))).trans
    ((RingedToposHom.TwoIso.associator (zariskiComparisonRinged S)
          (zariskiOverRingedMorphism S.toClosedFiber)
          (zariskiOverRingedMorphism (DividedPowerScheme.closedFiberι S.S))).trans
      (RingedToposHom.TwoIso.whiskerLeft.{u, u + 1, u + 1, u, u + 1, u + 1,
          u, u + 1, u + 1} (zariskiComparisonRinged S)
        (zariskiStructureTriangleRinged S)))

end ClosedFiber

end Crystalline.GlobalCrystallineSituation

end
