module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeBaseChange.PullbackSections
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization
public import StacksFrontier.AlgebraicGeometry.ProjTwistTheta.DegreeSection
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRestrictionConstruction

/-!
# Restriction of degree-one forms to a hyperplane is onto

The last open statement of [Stacks, Tag 08A7] over an infinite field — the `liftSection` clause of
`AlgebraicGeometry.HyperplaneRestrictionPackage`, in the geometric form that
`AlgebraicGeometry.nonempty_hyperplaneRestrictionPackage_of_surjective_restriction` hypothesises —
is that restriction of degree-one forms to a hyperplane is surjective on global sections of
`𝒪(1)`. This file proves it: on the `Proj k[T₀, …, Tₙ]` model, where a global section of `𝒪(1)` is
a linear form, and then on the base-change model `AlgebraicGeometry.projectiveSpaceOverRing`,
where the hyperplane restriction data of [Stacks, Tag 08A7] lives.

## Main definitions

* `AlgebraicGeometry.RestrictsOnto`: `Γ(Y, ℳ)` restricts onto `Γ(X, 𝒩)` along `j : X ⟶ Y` —
  there is an identification `θ : j^*ℳ ≅ 𝒩` for which `x ↦ θ(j^*x)` is surjective.

## Main results

* `AlgebraicGeometry.surjective_restriction_of_restrictsOnto`: **the identification does not
  matter.** If the restriction map is onto for one `θ : j^*ℳ ≅ 𝒩` it is onto for every one.
* `AlgebraicGeometry.restrictsOnto_of_isIso`, `AlgebraicGeometry.restrictsOnto_comp` and
  `AlgebraicGeometry.restrictsOnto_isoComp`: restricting onto along an isomorphism, along a
  composite, and along a composite whose first factor is an isomorphism.
* `Stacks.ProjectiveSpace.restrictsOnto_projMap`: **degree-one sections restrict onto `Proj ℬ`
  along `Proj ψ`**, for a surjective graded `ψ` with `𝒮` generated in degree one.
* `Stacks.ProjectiveSpace.exists_iso_restrictsOnto_hyperplane`: the same for the hyperplane of a
  nonzero degree-one form on `ℙⁿ_k`, together with the identification of [Stacks, Tag 089Z] it
  holds for.
* `AlgebraicGeometry.surjective_restriction_zeroScheme`: **restriction of degree-one forms to a
  hyperplane of `ℙ^{m+1}_k` is onto, on the base-change model** — for the zero scheme of a global
  section of `𝒪(1)` presented by a nonzero degree-one form, for *any* identification of it with
  `ℙᵐ_k` and *any* identification of the twists along the resulting closed immersion.

## The mathematics

The content is [Stacks, Tag 01MY] part (1): along `Proj ψ` the canonical section of a homogeneous
`a` restricts to the canonical section of `ψ a`
(`Stacks.AlgebraicGeometry.ProjTwistTheta.twistMap_degreeSection`). Surjectivity follows because
`ψ` is surjective in every degree
(`AlgebraicGeometry.Proj.gradedAddHom_surjective_of_surjective`) and because over a field every
global section of `𝒪(1)` *is* the canonical section of a degree-one form
(`Stacks.ProjectiveSpace.Cohomology.exists_degreeSection_eq`, [Stacks, Tag 01XS]). Everything
else is transport, and all of it is carried by `AlgebraicGeometry.RestrictsOnto`:

* Tag 01MY speaks about the morphism on the domain of definition `U(ψ)`, which for a surjective
  `ψ` is all of `Proj ℬ`, so `Proj ψ` is that morphism precomposed with an isomorphism;
* the hyperplane `Z(l)` is identified with `Proj ℬ` by [Stacks, Tag 089Z], and that
  identification composed with the inclusion *is* `Proj ψ`
  (`Stacks.ProjectiveSpace.exists_iso_zeroScheme_subscheme`);
* the `Proj` model and the base-change model are identified by
  `Stacks.ProjectiveCohomology.projModelIso`, compatibly with `𝒪(1)`
  (`Stacks.ProjectiveCohomology.pullbackProjModelIsoHomTwistOverIso`), and the zero scheme of a
  section corresponds to the zero scheme of its transport by [Stacks, Tag 0B6Y].

## Implementation notes

`AlgebraicGeometry.RestrictsOnto` is stated with an *existential* identification, and
`AlgebraicGeometry.surjective_restriction_of_restrictsOnto` turns it into the universal one. That
is what makes the transport cheap: two identifications of `j^*ℳ` with `𝒩` differ by an
automorphism of `𝒩`, which is bijective on sections, so no identification of twists ever has to
be matched with another — in particular the five-fold composite of pullback comparisons that
`AlgebraicGeometry.exists_iso_zeroScheme_projectiveSpaceOverRing` produces is never written down
here. For the same reason the statements quantify over the identification `φ` of the hyperplane
with `ℙᵐ_k`: two such differ by an automorphism of `ℙᵐ_k`, which
`AlgebraicGeometry.restrictsOnto_isoComp` absorbs as soon as *some* identification of the twists
along the composite is given — and that is what [Stacks, Tag 089Z] supplies.

## References

* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)
* [Stacks Project, Tag 089Z](https://stacks.math.columbia.edu/tag/089Z)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 01XS](https://stacks.math.columbia.edu/tag/01XS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare

universe u

namespace AlgebraicGeometry

/-! ### Restriction of global sections, and its transport -/

/-- **Restriction along `j` carries `Γ(Y, ℳ)` onto `Γ(X, 𝒩)`**: there is an identification
`θ : j^*ℳ ≅ 𝒩` for which every global section of `𝒩` is `θ` of the pullback of a global section
of `ℳ`. -/
def RestrictsOnto {X Y : Scheme.{u}} (j : X ⟶ Y) (M : Y.Modules) (N : X.Modules) : Prop :=
  ∃ θ : (Scheme.Modules.pullback j).obj M ≅ N,
    Function.Surjective fun x : Γ(M, ⊤) => θ.hom.app ⊤ (pullbackGlobalSections j M x)

/-- An isomorphism of sheaves of modules is bijective on sections, in the direction needed below:
the inverse read on sections is a right inverse. -/
theorem Scheme.Modules.app_hom_app_inv {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) (y : Γ(N, U)) : e.hom.app U (e.inv.app U y) = y :=
  congrArg (fun φ : N ⟶ N => (Scheme.Modules.Hom.app φ U) y) e.inv_hom_id

/-- The companion of `AlgebraicGeometry.Scheme.Modules.app_hom_app_inv`. -/
theorem Scheme.Modules.app_inv_app_hom {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) (y : Γ(M, U)) : e.inv.app U (e.hom.app U y) = y :=
  congrArg (fun φ : M ⟶ M => (Scheme.Modules.Hom.app φ U) y) e.hom_inv_id

/-- **The identification in `AlgebraicGeometry.RestrictsOnto` does not matter.** Two
identifications `j^*ℳ ≅ 𝒩` differ by an automorphism of `𝒩`, which is bijective on sections, so
surjectivity of the restriction map holds for one exactly when it holds for every one. -/
theorem surjective_restriction_of_restrictsOnto {X Y : Scheme.{u}} {j : X ⟶ Y} {M : Y.Modules}
    {N : X.Modules} (h : RestrictsOnto j M N)
    (θ : (Scheme.Modules.pullback j).obj M ≅ N) :
    Function.Surjective fun x : Γ(M, ⊤) => θ.hom.app ⊤ (pullbackGlobalSections j M x) := by
  obtain ⟨θ₀, h₀⟩ := h
  intro y
  obtain ⟨x, hx⟩ := h₀ ((θ₀.symm ≪≫ θ).inv.app ⊤ y)
  have hx' : θ₀.hom.app ⊤ (pullbackGlobalSections j M x)
      = (θ₀.symm ≪≫ θ).inv.app ⊤ y := hx
  refine ⟨x, ?_⟩
  change θ.hom.app ⊤ (pullbackGlobalSections j M x) = y
  have hθ : θ.hom = θ₀.hom ≫ (θ₀.symm ≪≫ θ).hom := by
    simp
  calc θ.hom.app ⊤ (pullbackGlobalSections j M x)
      = (θ₀.symm ≪≫ θ).hom.app ⊤ (θ₀.hom.app ⊤ (pullbackGlobalSections j M x)) :=
        congrArg (fun φ : (Scheme.Modules.pullback j).obj M ⟶ N =>
          (Scheme.Modules.Hom.app φ ⊤) (pullbackGlobalSections j M x)) hθ
    _ = y := by rw [hx']; exact Scheme.Modules.app_hom_app_inv _ ⊤ y

/-- **Restriction along an isomorphism is onto**, for any identification of the pullback. -/
theorem restrictsOnto_of_isIso {X Y : Scheme.{u}} (j : X ⟶ Y) [IsIso j] {M : Y.Modules}
    {N : X.Modules} (e : (Scheme.Modules.pullback j).obj M ≅ N) : RestrictsOnto j M N := by
  refine ⟨e, fun y => ?_⟩
  refine ⟨(Scheme.Modules.gammaTopIsoOfPullbackIso j e).inv y, ?_⟩
  exact (Scheme.Modules.gammaTopIsoOfPullbackIso_hom_apply j e _).symm.trans
    (Iso.inv_hom_id_apply (Scheme.Modules.gammaTopIsoOfPullbackIso j e) y)

/-- **Restriction onto is transitive.** If `Γ(Z, ℳ)` restricts onto `Γ(Y, 𝒩)` along `g` and
`Γ(Y, 𝒩)` restricts onto `Γ(X, 𝒫)` along `f`, then `Γ(Z, ℳ)` restricts onto `Γ(X, 𝒫)` along
`f ≫ g`. The identification is the comparison `(f ≫ g)^*ℳ ≅ f^*g^*ℳ` followed by `f^*` of the
first identification and then the second; `AlgebraicGeometry.pullbackGlobalSections_comp_hom`
factors the restriction map accordingly and naturality of the unit of `f^* ⊣ f_*` moves the
first identification past the second restriction. -/
theorem restrictsOnto_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {M : Z.Modules}
    {N : Y.Modules} {P : X.Modules} (hg : RestrictsOnto g M N) (hf : RestrictsOnto f N P) :
    RestrictsOnto (f ≫ g) M P := by
  obtain ⟨θg, hgs⟩ := hg
  obtain ⟨θf, hfs⟩ := hf
  refine ⟨((Scheme.Modules.pullbackComp f g).app M).symm ≪≫
    (Scheme.Modules.pullback f).mapIso θg ≪≫ θf, fun y => ?_⟩
  obtain ⟨z, hz⟩ := hfs y
  obtain ⟨x, hx⟩ := hgs z
  have hx' : θg.hom.app ⊤ (pullbackGlobalSections g M x) = z := hx
  have hz' : θf.hom.app ⊤ (pullbackGlobalSections f N z) = y := hz
  refine ⟨x, ?_⟩
  -- the restriction map along `f ≫ g`, factored
  have hcomp : pullbackGlobalSections (f ≫ g) M x =
      ((Scheme.Modules.pullbackComp f g).app M).hom.app ⊤
        (pullbackGlobalSections f ((Scheme.Modules.pullback g).obj M)
          (pullbackGlobalSections g M x)) := by
    rw [← pullbackGlobalSections_comp_hom f g M]
    rfl
  -- naturality of the unit in the module
  have hnat : ((Scheme.Modules.pullback f).map θg.hom).app ⊤
      (pullbackGlobalSections f ((Scheme.Modules.pullback g).obj M)
        (pullbackGlobalSections g M x))
      = pullbackGlobalSections f N (θg.hom.app ⊤ (pullbackGlobalSections g M x)) := by
    rw [pullbackGlobalSections_eq_unit f ((Scheme.Modules.pullback g).obj M),
      pullbackGlobalSections_eq_unit f N]
    exact Stacks.Divisors.pullbackGlobalSections_naturality f θg.hom
      (pullbackGlobalSections g M x)
  change θf.hom.app ⊤ (((Scheme.Modules.pullback f).map θg.hom).app ⊤
    (((Scheme.Modules.pullbackComp f g).app M).inv.app ⊤
      (pullbackGlobalSections (f ≫ g) M x))) = y
  rw [hcomp, Scheme.Modules.app_inv_app_hom ((Scheme.Modules.pullbackComp f g).app M) ⊤,
    hnat, hx', hz']

/-- The restriction map on global sections, read as the unit of `f^* ⊣ f_*` on an element. -/
alias pullbackGlobalSections_apply := SectionsEqualizer.pullbackGlobalSections_unit

/-- **Restriction along an isomorphism of schemes is onto on global sections.** -/
theorem surjective_pullbackGlobalSections_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (M : Y.Modules) :
    Function.Surjective fun x : Γ(M, ⊤) => pullbackGlobalSections f M x := fun y =>
  (surjective_restriction_of_restrictsOnto
    (restrictsOnto_of_isIso f (Iso.refl ((Scheme.Modules.pullback f).obj M)))
    (Iso.refl ((Scheme.Modules.pullback f).obj M)) y).imp fun _ h => h

/-- **Restriction onto, with the source reparametrised.** If `Γ(Y, ℳ)` restricts onto `Γ(X, 𝒩)`
along `j` and `σ : W ≅ X` is an isomorphism of schemes, then `Γ(Y, ℳ)` restricts onto `Γ(W, 𝒫)`
along `σ ≫ j` for **any** `𝒫` identified with `(σ ≫ j)^*ℳ`: the identification `σ^*𝒩 ≅ 𝒫` that
`AlgebraicGeometry.restrictsOnto_comp` needs is `σ^*` of the one for `j`, followed by the
comparison of pullbacks and the given identification. -/
theorem restrictsOnto_isoComp {W X Y : Scheme.{u}} (σ : W ⟶ X) [IsIso σ] (j : X ⟶ Y)
    {M : Y.Modules} {N : X.Modules} {P : W.Modules} (h : RestrictsOnto j M N)
    (e : (Scheme.Modules.pullback (σ ≫ j)).obj M ≅ P) : RestrictsOnto (σ ≫ j) M P := by
  obtain ⟨θ, -⟩ := id h
  exact restrictsOnto_comp σ j h (restrictsOnto_of_isIso σ
    ((Scheme.Modules.pullback σ).mapIso θ.symm ≪≫ (Scheme.Modules.pullbackComp σ j).app M ≪≫ e))

end AlgebraicGeometry

/-! ### The `Proj` model: restriction along `Proj ψ` -/

namespace Stacks.ProjectiveSpace

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S B σ τ : Type u} [CommRing S] [CommRing B] [SetLike σ S] [AddSubgroupClass σ S]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒮 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒮] [GradedRing ℬ]

/-- **[Stacks, Tag 01MY] part (1), at the `AlgebraicGeometry.pullbackGlobalSections`
spelling.** The comparison on the `n`-th twist carries the restriction of the canonical section
of a degree-`n` element `a` along `mapHom` to the restriction of the canonical section of `ψ a`
along the inclusion of the domain of definition.

This is `Stacks.AlgebraicGeometry.ProjTwistTheta.twistMap_degreeSection` with both units read as
restriction maps on global sections. -/
theorem twistMap_pullbackGlobalSections_degreeSection (ψ : 𝒮 →+*ᵍ ℬ) (n : ℕ) (a : 𝒮 n) :
    (Scheme.Modules.Hom.app ((projMapData 𝒮 ℬ ψ).twistMap (n : ℤ)) ⊤)
        (pullbackGlobalSections (mapHom 𝒮 ℬ ψ) (twistingSheafModule 𝒮 (n : ℤ))
          (degreeSection 𝒮 n a))
      = pullbackGlobalSections (mapDomain 𝒮 ℬ ψ).ι (twistingSheafModule ℬ (n : ℤ))
          (degreeSection ℬ n ⟨ψ a, ψ.map_mem a.2⟩) := by
  rw [AlgebraicGeometry.pullbackGlobalSections_apply (mapHom 𝒮 ℬ ψ)
      (twistingSheafModule 𝒮 (n : ℤ)) (degreeSection 𝒮 n a),
    AlgebraicGeometry.pullbackGlobalSections_apply (mapDomain 𝒮 ℬ ψ).ι
      (twistingSheafModule ℬ (n : ℤ)) (degreeSection ℬ n ⟨ψ a, ψ.map_mem a.2⟩)]
  exact Stacks.AlgebraicGeometry.ProjTwistTheta.twistMap_degreeSection 𝒮 ℬ ψ n a

/-- **Degree-one global sections restrict onto `Proj ℬ` along `Proj ψ`.** Let `ψ : 𝒮 ⟶ ℬ` be a
surjective homomorphism of graded rings with `𝒮` generated in degree one over `𝒮 0`, and suppose
every global section of `𝒪_{Proj ℬ}(1)` is the canonical section of a degree-one element of `ℬ`.
Then every global section of `𝒪_{Proj ℬ}(1)` is the restriction of a global section of
`𝒪_{Proj 𝒮}(1)` along `Proj ψ`.

The chain is [Stacks, Tag 01MY] part (1)
(`Stacks.ProjectiveSpace.twistMap_pullbackGlobalSections_degreeSection`), which carries the
canonical section of `a` to that of `ψ a` along the morphism on the domain of definition `U(ψ)`,
together with the two facts that make `U(ψ)` harmless: it is all of `Proj ℬ`
(`Stacks.AlgebraicGeometry.RelativeProjChain.mapDomain_eq_top_of_eventually_surjective`, since a
surjective graded homomorphism is surjective in every degree) and the comparison on the twist is
an isomorphism there ([Stacks, Tag 01N1] part (3)). Surjectivity of `ψ` in degree one lifts the
degree-one element of `ℬ` to one of `𝒮`. -/
theorem restrictsOnto_projMap (ψ : 𝒮 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒮).map ψ)
    (hsurj : Function.Surjective (ψ : S → B))
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤)
    (hlift : ∀ t : twistGlobalSections ℬ 1, ∃ b : ℬ 1, degreeSection ℬ 1 b = t) :
    AlgebraicGeometry.RestrictsOnto (Proj.map ψ hψ)
      (twistingSheafModule 𝒮 ((1 : ℕ) : ℤ)) (twistingSheafModule ℬ ((1 : ℕ) : ℤ)) := by
  have hev : ∀ᶠ d : ℕ in Filter.atTop,
      Function.Surjective (GradedRingHom.gradedAddHom ψ d) :=
    Filter.Eventually.of_forall fun d => Proj.gradedAddHom_surjective_of_surjective ψ hsurj d
  have hdom : mapDomain 𝒮 ℬ ψ = ⊤ :=
    Stacks.AlgebraicGeometry.RelativeProjChain.mapDomain_eq_top_of_eventually_surjective 𝒮 ℬ ψ hev
  have htw : IsIso ((projMapData 𝒮 ℬ ψ).twistMap ((1 : ℕ) : ℤ)) :=
    Stacks.AlgebraicGeometry.ProjTwistMono.isIso_projMapData_twistMap 𝒮 ℬ ψ hev hgen _
  set e : AlgebraicGeometry.Proj ℬ ⟶ (mapDomain 𝒮 ℬ ψ).toScheme :=
    (Scheme.topIso _).inv ≫ ((AlgebraicGeometry.Proj ℬ).isoOfEq hdom.symm).hom with he
  have he1 : e ≫ mapHom 𝒮 ℬ ψ = Proj.map ψ hψ := by
    rw [← Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map 𝒮 ℬ ψ hψ hdom,
      Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop, he, Category.assoc]
  have he2 : e ≫ (mapDomain 𝒮 ℬ ψ).ι = 𝟙 _ := by
    rw [he, Category.assoc]
    exact Stacks.AlgebraicGeometry.RelativeProj.topIso_inv_isoOfEq_hom_ι 𝒮 ℬ ψ hdom
  have hIsoE : IsIso e := by rw [he]; infer_instance
  have hιe : (mapDomain 𝒮 ℬ ψ).ι = inv e := IsIso.eq_inv_of_hom_inv_id he2
  have hIsoι : IsIso (mapDomain 𝒮 ℬ ψ).ι := by rw [hιe]; infer_instance
  rw [← he1]
  refine AlgebraicGeometry.restrictsOnto_comp e (mapHom 𝒮 ℬ ψ)
    (N := (Scheme.Modules.pullback (mapDomain 𝒮 ℬ ψ).ι).obj
      (twistingSheafModule ℬ ((1 : ℕ) : ℤ))) ?_ ?_
  · -- restriction along the morphism on the domain of definition
    refine ⟨@asIso _ _ _ _ _ htw, fun t => ?_⟩
    obtain ⟨u, hu⟩ := AlgebraicGeometry.surjective_pullbackGlobalSections_of_isIso
      (mapDomain 𝒮 ℬ ψ).ι (twistingSheafModule ℬ ((1 : ℕ) : ℤ)) t
    obtain ⟨b, hb⟩ := hlift u
    obtain ⟨a, ha⟩ := Proj.gradedAddHom_surjective_of_surjective ψ hsurj 1 b
    have hab : (⟨ψ a, ψ.map_mem a.2⟩ : ℬ 1) = b :=
      Subtype.ext ((GradedRingHom.gradedAddHom_apply_coe ψ 1 a).symm.trans
        (congrArg Subtype.val ha))
    refine ⟨degreeSection 𝒮 1 a,
      (twistMap_pullbackGlobalSections_degreeSection 𝒮 ℬ ψ 1 a).trans ?_⟩
    rw [hab, hb]
    exact hu
  · -- restriction along the isomorphism `Proj ℬ ≅ U(ψ)`
    refine AlgebraicGeometry.restrictsOnto_of_isIso e ?_
    refine (Scheme.Modules.pullbackComp e (mapDomain 𝒮 ℬ ψ).ι).app
      (twistingSheafModule ℬ ((1 : ℕ) : ℤ)) ≪≫ ?_
    refine (eqToIso (congrArg
      (fun φ => (Scheme.Modules.pullback φ).obj (twistingSheafModule ℬ ((1 : ℕ) : ℤ))) he2)) ≪≫ ?_
    exact (Scheme.Modules.pullbackId _).app (twistingSheafModule ℬ ((1 : ℕ) : ℤ))

/-! ### The hyperplane of a degree-one form on `ℙⁿ_k` -/

section Hyperplane

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {m : ℕ}

/-- **Degree-one global sections restrict onto the hyperplane of a nonzero degree-one form.**
For the identification `φ : ℙ^{n-1}_k ≅ Z(l)` of [Stacks, Tag 089Z] that
`Stacks.ProjectiveSpace.exists_iso_zeroScheme_subscheme` produces, every global section of
`𝒪(1)` on `ℙ^{n-1}_k` is the restriction of a global section of `𝒪(1)` on `ℙⁿ_k`.

The identification is reported together with the conclusion because the conclusion is about a
particular one: `φ` composed with the inclusion of the zero scheme *is* `Proj ψ` for the graded
surjection `ψ` cut out by `l`
(`Stacks.ProjectiveSpace.exists_gradedHom_ker_span_degreeOne`), which is what
`Stacks.ProjectiveSpace.restrictsOnto_projMap` speaks about; over a field the degree-one
hypothesis of that theorem is `Stacks.ProjectiveSpace.Cohomology.exists_degreeSection_eq`. Any
other identification is this one followed by an automorphism of `ℙ^{n-1}_k`, which
`AlgebraicGeometry.restrictsOnto_isoComp` absorbs once an identification of the twists along the
composite is given. -/
theorem exists_iso_restrictsOnto_hyperplane
    (l : MvPolynomial.homogeneousSubmodule (Fin (m + 2)) k 1)
    (hl : (l : MvPolynomial (Fin (m + 2)) k) ≠ 0) :
    ∃ φ : AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k) ≅
        (hyperplane l).subscheme,
      AlgebraicGeometry.RestrictsOnto (φ.hom ≫ (hyperplane l).subschemeι)
        (twistingSheafModule (MvPolynomial.homogeneousSubmodule (Fin (m + 2)) k) ((1 : ℕ) : ℤ))
        (twistingSheafModule (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k)
          ((1 : ℕ) : ℤ)) := by
  obtain ⟨ψ, hsurj, hker, -⟩ := exists_gradedHom_ker_span_degreeOne l hl
  obtain ⟨φ, hφ⟩ := exists_iso_zeroScheme_subscheme _ _ ψ
    (Proj.irrelevant_le_map_of_surjective ψ hsurj) hsurj
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (m + 2)) k) l hker
  have h := restrictsOnto_projMap _ _ ψ (Proj.irrelevant_le_map_of_surjective ψ hsurj) hsurj
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (m + 2)) k)
    (Cohomology.exists_degreeSection_eq m 1)
  rw [← hφ] at h
  exact ⟨φ, h⟩

end Hyperplane

end Stacks.ProjectiveSpace

/-! ### The base-change model: restriction onto the zero scheme of a degree-one section -/

namespace AlgebraicGeometry

open Stacks.ProjectiveCohomology (polyGrading projModelIso)
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The transport of `Stacks.ProjectiveSpace.exists_iso_restrictsOnto_hyperplane` across the
comparison of models, for a closed subscheme of `ℙ^{m+1}_k` whose inverse image on the `Proj`
model is the hyperplane of a nonzero degree-one form. The subscheme is a variable so that the
chain of identifications below is a chain of equalities of morphisms rather than of substitutions
inside a dependent type. -/
private theorem restrictsOnto_subschemeι_of_comap_eq_hyperplane (k : Type u) [Field k] (m : ℕ)
    (f : MvPolynomial (Fin (m + 2)) k) (hf : f ∈ polyGrading k (m + 1) 1) (hf0 : f ≠ 0)
    (J : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).IdealSheafData)
    (hJ : J.comap (projModelIso k (m + 1)).hom = Stacks.ProjectiveSpace.hyperplane ⟨f, hf⟩)
    (φ : projectiveSpaceOverRing m (CommRingCat.of k) ≅ J.subscheme)
    (θ1 : (Scheme.Modules.pullback (φ.hom ≫ J.subschemeι)).obj
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) ≅
      twistOver m (Spec (CommRingCat.of k)) 1) :
    RestrictsOnto (φ.hom ≫ J.subschemeι) (twistOver (m + 1) (Spec (CommRingCat.of k)) 1)
      (twistOver m (Spec (CommRingCat.of k)) 1) := by
  obtain ⟨φP, hP⟩ : ∃ φP : AlgebraicGeometry.Proj (polyGrading k m) ≅
      (J.comap (projModelIso k (m + 1)).hom).subscheme,
      RestrictsOnto (φP.hom ≫ (J.comap (projModelIso k (m + 1)).hom).subschemeι)
        (twistingSheafModule (polyGrading k (m + 1)) ((1 : ℕ) : ℤ))
        (twistingSheafModule (polyGrading k m) ((1 : ℕ) : ℤ)) := by
    rw [hJ]
    exact Stacks.ProjectiveSpace.exists_iso_restrictsOnto_hyperplane ⟨f, hf⟩ hf0
  obtain ⟨ψ, h2⟩ : ∃ ψ : projectiveSpaceOverRing m (CommRingCat.of k) ≅ J.subscheme,
      RestrictsOnto (ψ.hom ≫ J.subschemeι) (twistOver (m + 1) (Spec (CommRingCat.of k)) 1)
        (twistOver m (Spec (CommRingCat.of k)) 1) := by
    refine ⟨(projModelIso k m).symm ≪≫ φP ≪≫
      Stacks.Chow.comapSubschemeIsoOfIsIso (projModelIso k (m + 1)).hom J, ?_⟩
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [Stacks.Chow.comapSubschemeIsoOfIsIso_hom_subschemeι, ← Category.assoc φP.hom]
    refine restrictsOnto_comp (projModelIso k m).inv
      ((φP.hom ≫ (J.comap (projModelIso k (m + 1)).hom).subschemeι) ≫ (projModelIso k (m + 1)).hom)
      (N := twistingSheafModule (polyGrading k m) ((1 : ℕ) : ℤ)) ?_ ?_
    · exact restrictsOnto_comp (φP.hom ≫ (J.comap (projModelIso k (m + 1)).hom).subschemeι)
        (projModelIso k (m + 1)).hom
        (N := twistingSheafModule (polyGrading k (m + 1)) ((1 : ℕ) : ℤ))
        (restrictsOnto_of_isIso (projModelIso k (m + 1)).hom
          (Stacks.ProjectiveCohomology.pullbackProjModelIsoHomTwistOverIso k (m + 1) 1)) hP
    · exact restrictsOnto_of_isIso (projModelIso k m).inv
        (Scheme.Modules.pullbackInvObjIso (projModelIso k m)
          (Stacks.ProjectiveCohomology.pullbackProjModelIsoHomTwistOverIso k m 1))
  have hfac : (φ.hom ≫ ψ.inv) ≫ ψ.hom ≫ J.subschemeι = φ.hom ≫ J.subschemeι := by
    rw [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← hfac]
  exact restrictsOnto_isoComp _ _ h2
    (eqToIso (congrArg (fun ρ => (Scheme.Modules.pullback ρ).obj
      (twistOver (m + 1) (Spec (CommRingCat.of k)) 1)) hfac) ≪≫ θ1)

/-- **Restriction of degree-one forms to a hyperplane of `ℙ^{m+1}_k` is onto.** Let `v` be a
global section of `𝒪(1)` on the base-change model of `ℙ^{m+1}_k` corresponding to a nonzero
degree-one form `f` on `Proj k[T₀, …, T_{m+1}]`, let `φ` be *any* identification of `ℙᵐ_k` with
the zero scheme of `v` ([Stacks, Tag 089Z]) and let `θ1` be *any* identification of the pullback
of `𝒪(1)` along the resulting closed immersion `j = φ ≫ ι` with `𝒪(1)`. Then every global section
of `𝒪_{ℙᵐ}(1)` is `θ1` of the restriction along `j` of a global section of `𝒪_{ℙ^{m+1}}(1)`.

This is `Stacks.ProjectiveSpace.exists_iso_restrictsOnto_hyperplane` carried across the
comparison of models. The route is that of
`AlgebraicGeometry.exists_iso_zeroScheme_projectiveSpaceOverRing`: [Stacks, Tag 0B6Y]
identifies the inverse image of the zero scheme of `v` with the hyperplane of `f`, and the
identification of `ℙᵐ_k` with the zero scheme is the comparison of models followed by the one on
the `Proj` model and `Stacks.Chow.comapSubschemeIsoOfIsIso`. Only surjectivity on sections is
transported, and `AlgebraicGeometry.restrictsOnto_comp` composes it along that chain; neither the
identification of the twists along the comparison of models nor `θ1` itself has to be matched with
anything, because `AlgebraicGeometry.surjective_restriction_of_restrictsOnto` makes surjectivity
independent of the identification. -/
theorem surjective_restriction_zeroScheme (k : Type u) [Field k] (m : ℕ)
    (f : MvPolynomial (Fin (m + 2)) k) (hf : f ∈ polyGrading k (m + 1) 1) (hf0 : f ≠ 0)
    (v : Γ(twistOver (m + 1) (Spec (CommRingCat.of k)) 1, ⊤))
    (hv : ConcreteCategory.hom (twistGammaTopIso k (m + 1)).hom v
      = degreeSection (polyGrading k (m + 1)) 1 ⟨f, hf⟩)
    (φ : projectiveSpaceOverRing m (CommRingCat.of k) ≅
      (AlgebraicGeometry.zeroScheme (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) v).subscheme)
    (θ1 : (Scheme.Modules.pullback (φ.hom ≫ (AlgebraicGeometry.zeroScheme
          (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
          (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) v).subschemeι)).obj
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) ≅
      twistOver m (Spec (CommRingCat.of k)) 1) :
    Function.Surjective fun x : Γ(twistOver (m + 1) (Spec (CommRingCat.of k)) 1, ⊤) =>
      θ1.hom.app ⊤ (pullbackGlobalSections (φ.hom ≫ (AlgebraicGeometry.zeroScheme
          (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
          (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) v).subschemeι)
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) x) := by
  refine surjective_restriction_of_restrictsOnto
    (restrictsOnto_subschemeι_of_comap_eq_hyperplane k m f hf hf0 _ ?_ φ θ1) θ1
  have hE : ConcreteCategory.hom (Scheme.Modules.Hom.app
      (Stacks.ProjectiveCohomology.pullbackProjModelIsoHomTwistOverIso k (m + 1) 1).hom ⊤)
      (pullbackGlobalSections (projModelIso k (m + 1)).hom
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) v)
      = degreeSection (polyGrading k (m + 1)) 1 ⟨f, hf⟩ :=
    (Scheme.Modules.gammaTopIsoOfPullbackIso_hom_apply (projModelIso k (m + 1)).hom
      (Stacks.ProjectiveCohomology.pullbackProjModelIsoHomTwistOverIso k (m + 1) 1)
      v).symm.trans hv
  rw [← Stacks.Divisors.zeroScheme_pullback (projModelIso k (m + 1)).hom
    (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) v]
  exact AlgebraicGeometry.zeroScheme_eq_of_iso
    (Stacks.ProjectiveCohomology.pullbackProjModelIsoHomTwistOverIso k (m + 1) 1) hE

end AlgebraicGeometry

end
