module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModuleGraded
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTwistSheafMultiplication
import all StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModule
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Veronese comparison on twisted global sections

Let `S` be a graded ring, `d ≥ 1`, `S' = S⁽ᵈ⁾`, `i : X = Proj S ≅ X' = Proj S'` the Veronese
isomorphism of [Stacks, Tag 0B5J], `ℱ'` a sheaf of `𝒪_{X'}`-modules and `ℱ = i^*ℱ'`. Tag 0B5J's
assertion (2), tensored with `ℱ`, gives `ℱ(nd) ≅ i^*(ℱ'(n))`
(`Stacks.Veronese.veroneseTwistedModuleIso`); the unit of the pullback gives
`Γ(X', ℱ'(n)) ⟶ Γ(X, i^*(ℱ'(n)))`. This file composes the two into the comparison

`Γ(X', ℱ'(n)) ⟶ Γ(X, ℱ(nd))`

and proves it **bijective** — which is what makes the twisted global sections of `ℱ` in the
degrees divisible by `d` the same group as the twisted global sections of `ℱ'` in all degrees.
That is the geometric half of the Veronese reduction: on `X'` the graded ring `S⁽ᵈ⁾` is generated
in degree one for a suitable `d`
(`Stacks.Veronese.exists_finite_degreeOne_generators_veroneseSubring`,
`Stacks.Veronese.isNoetherianRing_veroneseGrading_zero`), so the whole degree-one theory applies
there, and this comparison is how its conclusions are read back on `X`, where `S` need not be
generated in degree one at all.

The comparison is *not* merely a bijection of abelian groups: it carries the degree-one scalar
action of `(S⁽ᵈ⁾)₁ = S_d` on `X'` to the action of `S_d` on `X`, by Tag 0B5J's compatibility with
the products of global sections of Tag 03GK
(`Stacks.Veronese.veroneseMultiplyHomogeneousSectionsCompatibility`). That compatibility is
stated there for the products
`AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyHomogeneousSections`, while the graded
`S`-module structure on `⨁_n Γ(X, ℱ(n))` is phrased with the scalar action
`Stacks.AlgebraicGeometry.ProjTwistedSections.homogeneousScalarTwistedSections`. This file
contains the bridge between those two, which is what makes the compatibility usable as a
statement about the module structure.

## Main results

* `Stacks.Veronese.veroneseTwistedSectionsComparison`: the comparison
  `Γ(X', ℱ'(n)) ⟶ Γ(X, ℱ(nd))`.
* `Stacks.Veronese.bijective_veroneseTwistedSectionsComparison`: it is bijective.
* `Stacks.Veronese.bijective_sheafIsoSections`: the general fact it rests on together with
  `Stacks.Veronese.bijective_modulesPullbackUnit` — an isomorphism of sheaves of modules is
  bijective on the sections over any open.
* `Stacks.Veronese.sheafSections_comp_eq_self`: what that bijectivity is read off — two morphisms
  of sheaves of modules composing to the identity compose to the identity on sections. It is
  stated separately because the semilinearity of the comparison needs the same identity for the
  inverse, where the compatibility square asks for the forward map.
* `Stacks.Veronese.multiplyTwistSections_degreeSection` and
  `Stacks.Veronese.multiplyByGlobalSection_degreeSection`: multiplying by the global section of
  `𝒪(i)` that a homogeneous `a` of degree `i` names is the morphism `𝒪(n) ⟶ 𝒪(i + n)`,
  respectively `ℱ(n) ⟶ ℱ(i + n)`, that `a` induces.
* `Stacks.Veronese.homogeneousScalarTwistedSections_eq_multiplyHomogeneousSections`: **the
  bridge.** The graded scalar action of Tag 03GK on the twisted global sections is the product of
  Tag 03GK against the section the scalar names.

## Implementation notes

The direction is from `X'` to `X`. That is the direction the Veronese reduction consumes: the
degree-one theory on `X'` produces a *generating* family of sections of `ℱ'(n)`, and what is
wanted is the family of sections of `ℱ(nd)` it names. The inverse direction is available from
the same bijectivity statement and needs no separate construction.

Bijectivity of the pullback-unit half is
`Stacks.Veronese.bijective_modulesPullbackUnit`, in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjVeroneseTwistSheafMultiplication.lean`, which
is where the surjective half already lived; it was generalised there rather than restated here.

The source and target are written as `(twistSheafOfModules … ).val.obj (op ⊤)`, the spelling
Tag 0B5J's statements use, rather than through the abbreviation
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistedSectionsComponent`; the two are the same
type by definition, so a consumer stated with the abbreviation may use these results directly.

## The transported scalar action, and where its two halves live

The Veronese comparison's effect on the sections a homogeneous element names is available:
`Stacks.Veronese.veroneseTwistingSheafIso_degreeSection`, in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjVeroneseGlobalSections.lean`, already states
exactly it: for `a` in the Veronese subring with `(a : S)` homogeneous of degree `n · d`, Tag
0B5J's isomorphism carries `degreeSection 𝒮 (n * d) a` to the pullback of
`degreeSection (veroneseGrading 𝒮 d) n a`. It is stated directly in the `degreeSection` spelling,
which is why a search for a conversion between that spelling and
`globalSectionsRingMap`/`DirectSum.component` does not find it — the conversion is internal to
its proof, through
`Stacks.Veronese.veroneseGlobalSectionsRingMapCompatibility_homogeneous`.

So both halves of the transported scalar action are available: that one for the scalars, and
`Stacks.Veronese.homogeneousScalarTwistedSections_eq_multiplyHomogeneousSections` here for the
action. Their *composite* — the semilinearity of
`Stacks.Veronese.veroneseTwistedSectionsAddEquiv` over the inclusion of the Veronese subring,
which is `Stacks.Veronese.veroneseMultiplyHomogeneousSectionsCompatibility` with both of its
correspondence hypotheses discharged and the degrees `(e + n)d = ed + nd` reconciled — is
`Stacks.Veronese.veroneseTwistedSectionsComparison_homogeneousScalarTwistedSections`, in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjVeroneseTwistedSectionsSemilinear.lean`. No
declaration *below* claims it; it is one import further on, because it needs assertion (2) on the
section a homogeneous element names, which lives in `ProjVeroneseGlobalSections.lean` and is not
in this file's import closure.

`Stacks.Veronese.multiplyByGlobalSection_degreeSection` and the bridge are stated for an
arbitrary sheaf of modules and carry no Veronese data; they are in this module because this is
where the Veronese comparison's consumers are, and so that there is one copy.

## References

* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open _root_.AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistSheafOfModules
  degreeSection multiplyHomogeneousSections multiplyTwistSections multiplyTwistSections_apply
  pureTensorSection pureTensorSection_hom_ext tensorSheafMap_pureTensorSection)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap twistSheafScalarMap
  homogeneousScalarTwistedSections)

namespace Stacks.Veronese

attribute [local instance_reducible] TopCat.Sheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w u₁ v₁

/-- The module pullback along an isomorphism of schemes is an equivalence, being left adjoint to
the pushforward, which is one. -/
private theorem isEquivalence_modulesPullback_of_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (Scheme.Modules.pullback g).IsEquivalence :=
  have : (Scheme.Modules.pushforward g).IsEquivalence :=
    AlgebraicGeometry.Scheme.Hom.pushforward_isEquivalence_of_isIso.{u, u} g
  (Scheme.Modules.pullbackPushforwardAdjunction g).isEquivalence_left_of_isEquivalence_right

/-- **The unit of the module pullback along an isomorphism of schemes is an isomorphism.** The
pushforward along an isomorphism is an equivalence, so its left adjoint is one too, and the unit
of an adjunction whose two functors are equivalences is invertible. -/
public theorem isIso_modulesPullbackPushforwardUnit_app {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (G : Y.Modules) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app G) :=
  have := isEquivalence_modulesPullback_of_isIso g
  inferInstance

/-- **The counit of the module pullback along an isomorphism of schemes is an isomorphism.** Same
argument as for the unit: pushforward along an isomorphism is an equivalence, so its left adjoint
is one too, and the counit of an adjunction whose two functors are equivalences is invertible.

This is the statement that *every* sheaf of modules on `X` is the pullback along `g` of one on
`Y` — namely of its own pushforward — which is how a statement proved on `Y` reaches an
arbitrary sheaf on `X`. -/
public theorem isIso_modulesPullbackPushforwardCounit_app {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsIso g] (F : X.Modules) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction g).counit.app F) :=
  have := isEquivalence_modulesPullback_of_isIso g
  inferInstance

/-- **Along an isomorphism of schemes, the pullback of sections over the preimage of an open is
bijective.** The unit of the adjunction is an isomorphism, and
`Stacks.Tag01VSPullbackTensor.modulesPullbackUnit` is its component at the open applied to the
section, so it inherits a two-sided inverse. -/
public theorem bijective_modulesPullbackUnit {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (G : Y.Modules) (W : Y.Opens) :
    Function.Bijective (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g G W) := by
  have := isIso_modulesPullbackPushforwardUnit_app g G
  set η := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app G
  refine ⟨fun s t hst => ?_, fun s => ⟨Scheme.Modules.Hom.app (inv η) W s, ?_⟩⟩
  · have h : Scheme.Modules.Hom.app (η ≫ inv η) W s = Scheme.Modules.Hom.app (η ≫ inv η) W t :=
      congrArg (Scheme.Modules.Hom.app (inv η) W) hst
    rwa [IsIso.hom_inv_id] at h
  · show Scheme.Modules.Hom.app (inv η ≫ η) W s = s
    rw [IsIso.inv_hom_id]
    rfl

/-- **Two morphisms of sheaves of modules composing to the identity compose to the identity on
the sections over an object.** Composition and the identity of sheaves of modules are computed
componentwise, so this is the hypothesis read at `U`. -/
public theorem sheafSections_comp_eq_self {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {P Q : SheafOfModules.{u} R} (φ : P ⟶ Q) (ψ : Q ⟶ P) (hc : φ ≫ ψ = 𝟙 P) (U : Cᵒᵖ)
    (x : P.val.obj U) :
    (ψ.val.app U).hom ((φ.val.app U).hom x) = x := by
  simpa using congrArg (fun f : P ⟶ P => (f.val.app U).hom x) hc

/-- **An isomorphism of sheaves of modules is bijective on the sections over an object.** The two
composites with the inverse's sections map are the sections map of an identity. -/
public theorem bijective_sheafIsoSections {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {A B : SheafOfModules.{u} R} (E : A ≅ B) (U : Cᵒᵖ) :
    Function.Bijective fun x : A.val.obj U => (E.hom.val.app U).hom x :=
  ⟨Function.LeftInverse.injective (sheafSections_comp_eq_self E.hom E.inv E.hom_inv_id U),
    Function.RightInverse.surjective (sheafSections_comp_eq_self E.inv E.hom E.inv_hom_id U)⟩

variable {S : Type u} {σ : Type w} [CommRing S]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **The Veronese comparison on twisted global sections**, `Γ(X', ℱ'(n)) ⟶ Γ(X, ℱ(nd))` for
`ℱ = i^*ℱ'`: the unit of the pullback followed by the inverse of Tag 0B5J's isomorphism
`ℱ(nd) ≅ i^*(ℱ'(n))`. -/
public def veroneseTwistedSectionsComparison (d : ℕ) (hd : 0 < d)
    (F' : letI := veroneseGradingGradedRing 𝒮 d hd
      SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top (veroneseGrading 𝒮 d)))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒮 d)))) (n : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    (twistSheafOfModules (veroneseGrading 𝒮 d) F' n).val.obj (op ⊤) →
      (twistSheafOfModules 𝒮 (pullbackProjModule 𝒮 (veroneseGrading 𝒮 d)
        (veroneseProjIso 𝒮 d hd).hom F') ((n : ℤ) * d)).val.obj (op ⊤) :=
  letI := veroneseGradingGradedRing 𝒮 d hd
  fun s' => ((veroneseTwistedModuleIso 𝒮 d hd F' n).inv.val.app (op ⊤)).hom
    (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
      (twistSheafOfModules (veroneseGrading 𝒮 d) F' n) ⊤ s')

/-- **The Veronese comparison on twisted global sections is bijective.** The sections of `ℱ(nd)`
on `X = Proj S` and the sections of `ℱ'(n)` on `X' = Proj S⁽ᵈ⁾` are the same group: the unit of
the pullback along the isomorphism `i` is bijective
(`Stacks.Veronese.bijective_modulesPullbackUnit`) and Tag 0B5J's comparison `ℱ(nd) ≅ i^*(ℱ'(n))`
is an isomorphism of sheaves, hence bijective on sections. -/
public theorem bijective_veroneseTwistedSectionsComparison (d : ℕ) (hd : 0 < d)
    (F' : letI := veroneseGradingGradedRing 𝒮 d hd
      SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top (veroneseGrading 𝒮 d)))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒮 d)))) (n : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    Function.Bijective (veroneseTwistedSectionsComparison 𝒮 d hd F' n) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  have : IsIso (veroneseProjIso 𝒮 d hd).hom := (veroneseProjIso 𝒮 d hd).isIso_hom
  exact Function.Bijective.comp
    (bijective_sheafIsoSections (veroneseTwistedModuleIso 𝒮 d hd F' n).symm (op ⊤))
    (bijective_modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
      (twistSheafOfModules (veroneseGrading 𝒮 d) F' n) ⊤)

/-- **The unit of the module pullback is additive on sections.** It is a component of a morphism
of sheaves of modules, so this is `map_add` of that component; it is recorded because
`Stacks.Tag01VSPullbackTensor.modulesPullbackUnit` is packaged as a bare function. -/
public theorem modulesPullbackUnit_add {X Y : Scheme.{u}} (g : X ⟶ Y) (G : Y.Modules)
    (W : Y.Opens) (x y : Γ(G, W)) :
    Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g G W (x + y) =
      Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g G W x +
        Stacks.Tag01VSPullbackTensor.modulesPullbackUnit g G W y :=
  map_add (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app G).val.app (op W)).hom x y

/-- **The Veronese comparison on twisted global sections, as an isomorphism of additive
groups**: `Γ(X', ℱ'(n)) ≃+ Γ(X, ℱ(nd))` for `ℱ = i^*ℱ'`.

This is `Stacks.Veronese.veroneseTwistedSectionsComparison` together with its bijectivity and its
additivity. Both halves of the comparison are components of morphisms of sheaves of modules —
the unit of the pullback and the inverse of Tag 0B5J's isomorphism — so additivity is `map_add`
twice. It is the form a consumer assembling the comparison into a module isomorphism needs; for
the compatibility with the scalar actions see
`Stacks.Veronese.homogeneousScalarTwistedSections_eq_multiplyHomogeneousSections` and
`Stacks.Veronese.veroneseMultiplyHomogeneousSectionsCompatibility`. -/
public def veroneseTwistedSectionsAddEquiv (d : ℕ) (hd : 0 < d)
    (F' : letI := veroneseGradingGradedRing 𝒮 d hd
      SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top (veroneseGrading 𝒮 d)))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒮 d)))) (n : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    (twistSheafOfModules (veroneseGrading 𝒮 d) F' n).val.obj (op ⊤) ≃+
      (twistSheafOfModules 𝒮 (pullbackProjModule 𝒮 (veroneseGrading 𝒮 d)
        (veroneseProjIso 𝒮 d hd).hom F') ((n : ℤ) * d)).val.obj (op ⊤) :=
  letI := veroneseGradingGradedRing 𝒮 d hd
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (veroneseTwistedSectionsComparison 𝒮 d hd F' n) fun x y =>
      ((congrArg ((veroneseTwistedModuleIso 𝒮 d hd F' n).inv.val.app (op ⊤)).hom
          (modulesPullbackUnit_add (veroneseProjIso 𝒮 d hd).hom
            (twistSheafOfModules (veroneseGrading 𝒮 d) F' n) ⊤ x y)).trans
        (map_add ((veroneseTwistedModuleIso 𝒮 d hd F' n).inv.val.app (op ⊤)).hom _ _)))
    (bijective_veroneseTwistedSectionsComparison 𝒮 d hd F' n)

/-- The additive equivalence `veroneseTwistedSectionsAddEquiv` sends a section `s'` of `ℱ'(n)`
to its image under `veroneseTwistedSectionsComparison`. -/
@[simp]
public theorem veroneseTwistedSectionsAddEquiv_apply (d : ℕ) (hd : 0 < d)
    (F' : letI := veroneseGradingGradedRing 𝒮 d hd
      SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top (veroneseGrading 𝒮 d)))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒮 d)))) (n : ℤ)
    (s' : letI := veroneseGradingGradedRing 𝒮 d hd
      (twistSheafOfModules (veroneseGrading 𝒮 d) F' n).val.obj (op ⊤)) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    veroneseTwistedSectionsAddEquiv 𝒮 d hd F' n s' =
      veroneseTwistedSectionsComparison 𝒮 d hd F' n s' :=
  rfl

/-! ### The graded scalar action is multiplication by the section the scalar names -/

/-- A localized fraction with denominator `1` multiplies as its numerator acts. -/
private lemma mk_one_mul_eq_map {P : Submonoid S} (a : S) (z : LocalizedModule P S) :
    LocalizedModule.mk a (1 : P) * z = LocalizedModule.map P (LinearMap.mul S S a) z := by
  induction z using LocalizedModule.induction_on with
  | h m t =>
      rw [LocalizedModule.map_mk, ← smul_eq_mul]
      refine (LocalizedModule.mk_smul_mk a m 1 t).trans ?_
      rw [one_mul]
      rfl

/-- **Multiplication by the global section of `𝒪(i)` that a homogeneous `a` of degree `i` names
is the morphism `𝒪(n) ⟶ 𝒪(i + n)` that `a` induces.** Both sides are read pointwise: the twist
section has value `a / 1` at every point, multiplication in the fibre by `a / 1` is the action of
`a`, and the morphism of twisting sheaves is the associated-sheaf image of multiplication by
`a`. -/
public theorem multiplyTwistSections_degreeSection (i : ℕ) (n : ℤ) (a : 𝒮 i)
    (U : Opens (ProjectiveSpectrum.top 𝒮)) (c : (twistingSheaf 𝒮 n).val.obj (op U)) :
    multiplyTwistSections 𝒮 (i : ℤ) n U
        ((twistingSheaf 𝒮 (i : ℤ)).val.map (homOfLE le_top).op (degreeSection 𝒮 i a)) c =
      (twistScalarSheafMap 𝒮 i n ((i : ℤ) + n) rfl a).val.app (op U) c := by
  refine AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSectionsOn_ext 𝒮 fun x => ?_
  have hval : ((twistingSheaf 𝒮 (i : ℤ)).val.map (homOfLE le_top).op
      (degreeSection 𝒮 i a)).1 x =
      LocalizedModule.mk (a : S) (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSections_restrict_top_apply 𝒮
      (degreeSection 𝒮 i a) U x).trans
      (Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection_apply 𝒮 i a _)
  refine (multiplyTwistSections_apply 𝒮 (i : ℤ) n U _ c x).trans ?_
  refine (congrArg (fun r => r * c.1 x) hval).trans ?_
  exact mk_one_mul_eq_map (a : S) (c.1 x)

variable (F : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))

/-- **Multiplication of `ℱ(n)` by the global section of `𝒪(i)` that a homogeneous `a` of degree
`i` names is the graded scalar action of `a`**, as morphisms `ℱ(n) ⟶ ℱ(i + n)`.

Both are the identity of `ℱ` tensored with a morphism of twisting sheaves, so the identity is
checked on the sections determined by a pair of sections
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.pureTensorSection_hom_ext`), where it is
`multiplyTwistSections_degreeSection`. No transport of degrees appears: multiplication by a
section of `𝒪(i)` lands in `ℱ(i + n)` on the nose. -/
private theorem multiplyByGlobalSection_degreeSection (i : ℕ) (n : ℤ) (a : 𝒮 i) :
    AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyByGlobalSection 𝒮 F (i : ℤ) n
        (degreeSection 𝒮 i a) =
      twistSheafScalarMap 𝒮 F i n ((i : ℤ) + n) rfl a := by
  refine pureTensorSection_hom_ext 𝒮 F (twistingSheaf 𝒮 n) _ ?_
  intro U b c
  refine (AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyByGlobalSection_pure 𝒮 F (i : ℤ) n
    (degreeSection 𝒮 i a) U b c).trans ?_
  refine Eq.trans ?_ (tensorSheafMap_pureTensorSection 𝒮 F (twistingSheaf 𝒮 n) F
    (twistingSheaf 𝒮 ((i : ℤ) + n)) (𝟙 F) (twistScalarSheafMap 𝒮 i n ((i : ℤ) + n) rfl a)
    U b c).symm
  exact congrArg (pureTensorSection 𝒮 F (twistingSheaf 𝒮 ((i : ℤ) + n)) U b)
    (multiplyTwistSections_degreeSection 𝒮 i n a U c)

/-- **Identification (i): the graded scalar action of [Stacks, Tag 03GK] on the twisted global
sections is the product of Tag 03GK against the global section of `𝒪(i)` that the scalar
names.**

`Stacks.AlgebraicGeometry.ProjTwistedSections.homogeneousScalarTwistedSections` is the action the
graded `S`-module structure on `⨁_n Γ(X, ℱ(n))` is built from, and so the action that
`Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep.degreeOneSections` and
`Stacks.AlgebraicGeometry.ProjTwistedSections.TwistedGlobalSectionsModule` are phrased with;
`AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyHomogeneousSections` is the product that
[Stacks, Tag 0B5J]'s compatibility
`Stacks.Veronese.veroneseMultiplyHomogeneousSectionsCompatibility` is stated for. This is the
bridge between them, and it is what lets a degree-one generation statement proved on
`Proj S⁽ᵈ⁾` be read as a statement about the module structure on `Proj S`.

The two sides are *not* two morphisms applied to the same argument — the left is
`(𝟙_ℱ ⊗ σ_a)` evaluated at `t`, the right tensors `t` with the section first — so the identity
cannot be checked on pure tensors in `t`, and `t` is a section of a sheafified tensor product and
is not a sum of pure tensors. What makes it provable is
`AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyByGlobalSection`, multiplication by a global
section *as a morphism*: through it both sides become components of morphisms out of
`ℱ ⊗ 𝒪(n)`, and `multiplyByGlobalSection_degreeSection` identifies those. -/
@[ega "II 2.6.4" "(F)"]
public theorem homogeneousScalarTwistedSections_eq_multiplyHomogeneousSections
    (i : ℕ) (n : ℤ) (a : 𝒮 i) (t : (twistSheafOfModules 𝒮 F n).val.obj (op ⊤)) :
    homogeneousScalarTwistedSections 𝒮 F i n a t =
      multiplyHomogeneousSections 𝒮 F i n (degreeSection 𝒮 i a) t := by
  refine Eq.trans ?_
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.multiplyHomogeneousSections_eq 𝒮 F i n
      (degreeSection 𝒮 i a) t).symm
  exact congrArg (fun φ : twistSheafOfModules 𝒮 F n ⟶ twistSheafOfModules 𝒮 F ((i : ℤ) + n) =>
    φ.val.app (op ⊤) t) (multiplyByGlobalSection_degreeSection 𝒮 F i n a).symm

end Stacks.Veronese

end
