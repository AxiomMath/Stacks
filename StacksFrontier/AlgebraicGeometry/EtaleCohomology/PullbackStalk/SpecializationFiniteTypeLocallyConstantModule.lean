module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Specialization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantWeakSerre

/-!
# Stalks and specialization maps of a finite type locally constant sheaf of modules

Let `S` be a scheme, let `Λ` be a ring and let `F` be a sheaf of `Λ`-modules on the small étale
site of `S` which is locally constant of finite type, i.e. which becomes, on a covering of every
object of the site, the constant sheaf attached to a finitely generated `Λ`-module. Covering the
final object `S / S` by objects on which `F` becomes constant, every geometric point of `S` lifts
to a member `U` of that covering, and over `U` the sheaf is comparable to a constant presheaf by
a locally bijective map. That comparison identifies the finitely generated value with the stalk
at the geometric point and is compatible with specialization, so the stalks are finitely
generated `Λ`-modules and the specialization maps are bijective.

This is the implication (1) ⟹ (2) of Tag 0GKC, the module-coefficient analogue of Tag 0GJ7.
The converse implication (2) ⟹ (1) and the equivalence itself are proved in the downstream file
`SpecializationFiniteTypeLocallyConstantModuleConverse.lean` of this directory, as
`AlgebraicGeometry.isFiniteTypeLocallyConstantModuleSheaf_of_isFG_etaleStalk` and
`AlgebraicGeometry.isFiniteTypeLocallyConstantModuleSheaf_iff_isFG_etaleStalk_and_bijective`.

## Main definitions

* `AlgebraicGeometry.moduleConstantGerm` — the germ at a geometric point of the section attached
  to an element of a module `E` by a comparison map from the constant presheaf on `E`.

## Main results

* `AlgebraicGeometry.bijective_moduleConstantGerm` — a locally bijective comparison map from a
  constant presheaf identifies its value with the stalk.
* `AlgebraicGeometry.specializationMapOnStalks_moduleConstantGerm` — the specialization map
  carries germs of such sections to germs of the same sections.
* `AlgebraicGeometry.isFG_etaleStalk_of_isFiniteTypeLocallyConstantModuleSheaf` and
  `AlgebraicGeometry.bijective_specializationMapOnStalks_of_isFiniteTypeLocallyConstantModuleSheaf`
  — the two halves of the implication (1) ⟹ (2) of Tag 0GKC.
* `AlgebraicGeometry.isFiniteTypeLocallyConstantModuleSheaf_iff_stalks_and_specialization`
  — the equivalence of Tag 0GKC derived from a supplied proof `hconverse` of the converse
  implication; the equivalence with no such argument is
  `AlgebraicGeometry.isFiniteTypeLocallyConstantModuleSheaf_iff_isFG_etaleStalk_and_bijective`.

## Implementation notes

"Finite `Λ`-module" is read as "finitely generated `Λ`-module", which is the source's meaning of
*finite module*; it is `ModuleCat.isFG`, not finiteness of the underlying set.

The germ calculus is the one of
`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber`, available for a presheaf with values
in any concrete category whose forgetful functor preserves the filtered colimits indexing the
stalk; for `ModuleCat` that preservation is
`AlgebraicGeometry.preservesFilteredColimitsOfSize_forget_moduleCat`. Local injectivity and local
surjectivity of the comparison map are hypotheses for the localized topology, and the sieves they
provide are transported to the small étale site itself by
`CategoryTheory.GrothendieckTopology.mem_over_iff` before the joint surjectivity property of the
point attached to the geometric point is applied to them.

The implication (1) ⟹ (2) proved here uses neither the hypothesis on the irreducible
components of `S` nor the Noetherian hypothesis on `Λ`. The converse implication, which constructs
an étale neighbourhood trivializing `F` out of a presentation of the stalk, is proved in the
downstream file `SpecializationFiniteTypeLocallyConstantModuleConverse.lean` of this directory,
using the openness of the locus where a comparison map is bijective and the ascent of the
finitely-many-irreducible-components hypothesis along an étale morphism (Tag 0BAL,
`AlgebraicGeometry.finiteIrreducibleComponents_of_etale`).

## References

* [Stacks Project, Tag 0GKC](https://stacks.math.columbia.edu/tag/0GKC)
* [Stacks Project, Tag 0GJ7](https://stacks.math.columbia.edu/tag/0GJ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf

universe u r

attribute [local instance] AlgebraicGeometry.preservesFilteredColimitsOfSize_forget_moduleCatMax

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Λ : Type r)
  [CommRing Λ] {U : SmallEtale B S hS} {E : ModuleCat.{max (u + 1) r} Λ}
  {P : (SmallEtale B S hS)ᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ}

/-- The germ at a geometric point `s`, through a lift `x` of `s` to `U`, of the section of `P`
over `U` attached to an element of `E` by a comparison map from the constant presheaf, as a map
of `Λ`-modules out of `E`. -/
public def moduleConstantGerm (s : GeometricPoint S)
    (x : (geometricPointFiber B S hS s).obj U)
    (ψ : (Functor.const (Over U)ᵒᵖ).obj E ⟶ (Over.forget U).op ⋙ P) :
    E ⟶ etaleStalk B S hS s P :=
  ψ.app (op (Over.mk (𝟙 U))) ≫ (geometricPointSitePoint B S hS s).toPresheafFiber U x P

/-- A comparison map from the constant presheaf with value `E` on `Over U` is determined by its
value at the identity of `U`: on an object `V` it is that value followed by the restriction
along `V.hom`. -/
public theorem moduleConstantPresheafHom_app (V : Over U)
    (ψ : (Functor.const (Over U)ᵒᵖ).obj E ⟶ (Over.forget U).op ⋙ P) :
    ψ.app (op V) = ψ.app (op (Over.mk (𝟙 U))) ≫ P.map V.hom.op := by
  have h := ψ.naturality (Over.homMk V.hom (by simp) : V ⟶ Over.mk (𝟙 U)).op
  simpa using h

/-- The elementwise form of `AlgebraicGeometry.moduleConstantPresheafHom_app`. -/
public theorem moduleConstantPresheafHom_app_apply (V : Over U)
    (ψ : (Functor.const (Over U)ᵒᵖ).obj E ⟶ (Over.forget U).op ⋙ P) (e : ToType E) :
    ψ.app (op V) e = P.map V.hom.op (ψ.app (op (Over.mk (𝟙 U))) e) :=
  ConcreteCategory.congr_hom (moduleConstantPresheafHom_app B S hS Λ V ψ) e

/-- A comparison map from the constant presheaf on `E` over `U` which is locally bijective
identifies `E` with the stalk of `P` at any geometric point having a lift to `U`. -/
public theorem bijective_moduleConstantGerm (s : GeometricPoint S)
    (x : (geometricPointFiber B S hS s).obj U)
    (ψ : (Functor.const (Over U)ᵒᵖ).obj E ⟶ (Over.forget U).op ⋙ P)
    (hinj : Presheaf.IsLocallyInjective ((SmallEtale.topology B S hS).over U) ψ)
    (hsurj : Presheaf.IsLocallySurjective ((SmallEtale.topology B S hS).over U) ψ) :
    Function.Bijective (moduleConstantGerm B S hS Λ s x ψ) := by
  let Φ := geometricPointSitePoint B S hS s
  constructor
  · intro e e' heq
    replace heq : Φ.toPresheafFiber U x P (ψ.app (op (Over.mk (𝟙 U))) e) =
        Φ.toPresheafFiber U x P (ψ.app (op (Over.mk (𝟙 U))) e') := heq
    obtain ⟨Y, f, y, -, hfe⟩ := (Φ.toPresheafFiber_eq_iff' U x _ _).1 heq
    have happ : ψ.app (op (Over.mk f)) e = ψ.app (op (Over.mk f)) e' := by
      rw [moduleConstantPresheafHom_app_apply B S hS Λ (Over.mk f) ψ e,
        moduleConstantPresheafHom_app_apply B S hS Λ (Over.mk f) ψ e']
      exact hfe
    have hmem := hinj.equalizerSieve_mem (X := op (Over.mk f)) e e' happ
    rw [GrothendieckTopology.mem_over_iff] at hmem
    obtain ⟨Z, g, hg, -, -⟩ := Φ.jointly_surjective _ hmem y
    rw [Sieve.overEquiv_iff] at hg
    simpa using hg
  · intro z
    obtain ⟨W, w, c, hc⟩ := Φ.toPresheafFiber_jointly_surjective (P := P) z
    let ZW : Φ.fiber.Elements := Functor.elementsMk Φ.fiber W w
    let ZU : Φ.fiber.Elements := Functor.elementsMk Φ.fiber U x
    let Z : Φ.fiber.Elements := IsCofiltered.min ZW ZU
    let m : Z.1 ⟶ W := (IsCofiltered.minToLeft ZW ZU).1
    let k : Z.1 ⟶ U := (IsCofiltered.minToRight ZW ZU).1
    have hm : Φ.fiber.map m Z.2 = w := (IsCofiltered.minToLeft ZW ZU).2
    have hk : Φ.fiber.map k Z.2 = x := (IsCofiltered.minToRight ZW ZU).2
    have hz : Φ.toPresheafFiber Z.1 Z.2 P (P.map m.op c) = z := by
      rw [Φ.toPresheafFiber_w_apply m Z.2 P c, hm]
      exact hc
    have hmem := hsurj.imageSieve_mem (U := Over.mk k) (P.map m.op c)
    rw [GrothendieckTopology.mem_over_iff] at hmem
    obtain ⟨Y, g, hg, y, hy⟩ := Φ.jointly_surjective _ hmem Z.2
    rw [Sieve.overEquiv_iff] at hg
    obtain ⟨e, he⟩ := hg
    refine ⟨e, ?_⟩
    have hval : P.map (g ≫ k).op (ψ.app (op (Over.mk (𝟙 U))) e) =
        P.map g.op (P.map m.op c) :=
      (moduleConstantPresheafHom_app_apply B S hS Λ (Over.mk (g ≫ k)) ψ e).symm.trans he
    have hgy : Φ.fiber.map (g ≫ k) y = x := by
      rw [Φ.fiber.map_comp, CategoryTheory.comp_apply, hy]
      exact hk
    change Φ.toPresheafFiber U x P (ψ.app (op (Over.mk (𝟙 U))) e) = z
    rw [← hgy, ← Φ.toPresheafFiber_w_apply (g ≫ k) y P, hval,
      Φ.toPresheafFiber_w_apply g y P, hy]
    exact hz

/-- A locally bijective comparison map from a constant presheaf with finitely generated value
makes the stalk at any geometric point with a lift to `U` a finitely generated `Λ`-module. -/
public theorem isFG_etaleStalk_of_bijective_moduleConstantGerm (hE : ModuleCat.isFG Λ E)
    (s : GeometricPoint S) (x : (geometricPointFiber B S hS s).obj U)
    (ψ : (Functor.const (Over U)ᵒᵖ).obj E ⟶ (Over.forget U).op ⋙ P)
    (hinj : Presheaf.IsLocallyInjective ((SmallEtale.topology B S hS).over U) ψ)
    (hsurj : Presheaf.IsLocallySurjective ((SmallEtale.topology B S hS).over U) ψ) :
    ModuleCat.isFG Λ (etaleStalk B S hS s P) := by
  have hiso : IsIso (moduleConstantGerm B S hS Λ s x ψ) := by
    have : IsIso ((forget (ModuleCat.{max (u + 1) r} Λ)).map (moduleConstantGerm B S hS Λ s x ψ)) :=
      (bijective_iff_isIso_ofHom _).mp
        (bijective_moduleConstantGerm B S hS Λ s x ψ hinj hsurj)
    exact isIso_of_reflects_iso _ (forget (ModuleCat.{max (u + 1) r} Λ))
  rw [ModuleCat.isFG_iff] at hE ⊢
  exact Module.Finite.equiv (asIso (moduleConstantGerm B S hS Λ s x ψ)).toLinearEquiv

/-- The canonical map from the sections over an étale neighbourhood into the stalk, followed by
the specialization map, is the canonical map at the specialized neighbourhood. -/
public theorem toPresheafFiber_comp_specializationMapOnStalks {s : GeometricPoint S}
    (σ : GeometricSpecialization B S hS s) (x : (geometricPointFiber B S hS s).obj U) :
    (geometricPointSitePoint B S hS s).toPresheafFiber U x P ≫ specializationMapOnStalks σ P =
      (geometricPointSitePoint B S hS σ.target).toPresheafFiber U
        ((specializationFiberHom σ).app U x) P :=
  ι_comp_specializationMapOnStalks σ P (Functor.elementsMk (geometricPointFiber B S hS s) U x)

/-- The specialization map carries the germ at `s` of the section attached to an element of `E`
to the germ of the same section at the specialized geometric point. -/
public theorem specializationMapOnStalks_moduleConstantGerm {s : GeometricPoint S}
    (σ : GeometricSpecialization B S hS s) (x : (geometricPointFiber B S hS s).obj U)
    (ψ : (Functor.const (Over U)ᵒᵖ).obj E ⟶ (Over.forget U).op ⋙ P) :
    moduleConstantGerm B S hS Λ s x ψ ≫ specializationMapOnStalks σ P =
      moduleConstantGerm B S hS Λ σ.target ((specializationFiberHom σ).app U x) ψ :=
  (Category.assoc (ψ.app (op (Over.mk (𝟙 U))))
      ((geometricPointSitePoint B S hS s).toPresheafFiber U x P)
      (specializationMapOnStalks σ P)).trans
    (congrArg (fun k => ψ.app (op (Over.mk (𝟙 U))) ≫ k)
      (toPresheafFiber_comp_specializationMapOnStalks B S hS Λ σ x))

/-- If a geometric point lifts to an object over which `P` is comparable to a constant presheaf
by a locally bijective map, the specialization map to any specialization of it is bijective. -/
public theorem bijective_specializationMapOnStalks_of_moduleConstantGerm
    {s : GeometricPoint S} (σ : GeometricSpecialization B S hS s)
    (x : (geometricPointFiber B S hS s).obj U)
    (ψ : (Functor.const (Over U)ᵒᵖ).obj E ⟶ (Over.forget U).op ⋙ P)
    (hinj : Presheaf.IsLocallyInjective ((SmallEtale.topology B S hS).over U) ψ)
    (hsurj : Presheaf.IsLocallySurjective ((SmallEtale.topology B S hS).over U) ψ) :
    Function.Bijective (specializationMapOnStalks σ P) := by
  have hs := bijective_moduleConstantGerm B S hS Λ s x ψ hinj hsurj
  have ht := bijective_moduleConstantGerm B S hS Λ σ.target
    ((specializationFiberHom σ).app U x) ψ hinj hsurj
  have hcomp := specializationMapOnStalks_moduleConstantGerm B S hS Λ σ x ψ
  have hcompapp : ∀ e, specializationMapOnStalks σ P (moduleConstantGerm B S hS Λ s x ψ e) =
      moduleConstantGerm B S hS Λ σ.target ((specializationFiberHom σ).app U x) ψ e := by
    intro e
    simpa using ConcreteCategory.congr_hom hcomp e
  constructor
  · intro a b hab
    obtain ⟨ea, rfl⟩ := hs.2 a
    obtain ⟨eb, rfl⟩ := hs.2 b
    rw [hcompapp, hcompapp] at hab
    exact congrArg _ (ht.1 hab)
  · intro c
    obtain ⟨e, he⟩ := ht.2 c
    exact ⟨moduleConstantGerm B S hS Λ s x ψ e, (hcompapp e).trans he⟩

/-! ### The implication (1) ⟹ (2) of Tag 0GKC -/

/-- At every geometric point of `S`, a finite type locally constant sheaf of `Λ`-modules on the
small étale site is comparable, over some étale neighbourhood of the point, to a constant
presheaf with finitely generated value by a locally bijective map. -/
public theorem exists_locallyBijective_constantHom_of_isFiniteTypeLocallyConstantModuleSheaf
    (F : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{max (u + 1) r} Λ))
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
      (SmallEtale.topology B S hS) Λ F)
    (s : GeometricPoint S) :
    ∃ (V : SmallEtale B S hS) (_x : (geometricPointFiber B S hS s).obj V)
      (E : ModuleCat.{max (u + 1) r} Λ), ModuleCat.isFG Λ E ∧
      ∃ ψ : (Functor.const (Over V)ᵒᵖ).obj E ⟶ (Over.forget V).op ⋙ F.obj,
        Presheaf.IsLocallyInjective ((SmallEtale.topology B S hS).over V) ψ ∧
          Presheaf.IsLocallySurjective ((SmallEtale.topology B S hS).over V) ψ := by
  obtain ⟨I, X, f, hcov, hconst⟩ := hF (SmallEtale.final B S hS)
  obtain ⟨W, g, hg, w, -⟩ := (geometricPointSitePoint B S hS s).jointly_surjective _ hcov
    ((geometricPointSitePoint B S hS s).uniqueFiberObj (SmallEtale.final B S hS)
      (SmallEtale.finalIsTerminal B S hS)).default
  obtain ⟨-, k, -, ⟨i⟩, rfl⟩ := hg
  obtain ⟨E, hE, ⟨ε⟩⟩ := hconst i
  obtain ⟨δ⟩ : Nonempty (sheafify ((SmallEtale.topology B S hS).over (X i))
      ((Functor.const (Over (X i))ᵒᵖ).obj E) ≅ (Over.forget (X i)).op ⋙ F.obj) :=
    ⟨(sheafToPresheaf ((SmallEtale.topology B S hS).over (X i))
      (ModuleCat.{max (u + 1) r} Λ)).mapIso ε⟩
  have hinj := isLocallyInjective_toSheafify_moduleCat.{u, u + 1, r}
    ((SmallEtale.topology B S hS).over (X i)) Λ ((Functor.const (Over (X i))ᵒᵖ).obj E)
  have hsurj := isLocallySurjective_toSheafify_moduleCat.{u, u + 1, r}
    ((SmallEtale.topology B S hS).over (X i)) Λ ((Functor.const (Over (X i))ᵒᵖ).obj E)
  exact ⟨X i, (geometricPointFiber B S hS s).map k w, E, hE,
    toSheafify ((SmallEtale.topology B S hS).over (X i))
      ((Functor.const (Over (X i))ᵒᵖ).obj E) ≫ δ.hom, inferInstance, inferInstance⟩

/-- The implication (1) ⟹ (2) of Stacks Project, Tag 0GKC, first half: the stalk at a
geometric point of a finite type locally constant sheaf of `Λ`-modules on the small étale site
of a scheme is a finitely generated `Λ`-module. -/
public theorem isFG_etaleStalk_of_isFiniteTypeLocallyConstantModuleSheaf
    (F : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{max (u + 1) r} Λ))
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
      (SmallEtale.topology B S hS) Λ F)
    (s : GeometricPoint S) :
    ModuleCat.isFG Λ (etaleStalk B S hS s F.obj) := by
  obtain ⟨V, x, E, hE, ψ, hinj, hsurj⟩ :=
    exists_locallyBijective_constantHom_of_isFiniteTypeLocallyConstantModuleSheaf
      B S hS Λ F hF s
  exact isFG_etaleStalk_of_bijective_moduleConstantGerm B S hS Λ hE s x ψ hinj hsurj

/-- The implication (1) ⟹ (2) of Stacks Project, Tag 0GKC, second half: every specialization
map between stalks of a finite type locally constant sheaf of `Λ`-modules on the small étale
site of a scheme is bijective. -/
@[sga "4 IX 2.13" "(i)"]
public theorem bijective_specializationMapOnStalks_of_isFiniteTypeLocallyConstantModuleSheaf
    (F : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{max (u + 1) r} Λ))
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
      (SmallEtale.topology B S hS) Λ F)
    (s : GeometricPoint S) (σ : GeometricSpecialization B S hS s) :
    Function.Bijective (specializationMapOnStalks σ F.obj) := by
  obtain ⟨V, x, E, hE, ψ, hinj, hsurj⟩ :=
    exists_locallyBijective_constantHom_of_isFiniteTypeLocallyConstantModuleSheaf
      B S hS Λ F hF s
  exact bijective_specializationMapOnStalks_of_moduleConstantGerm B S hS Λ σ x ψ hinj hsurj

/-! ### The equivalence of Tag 0GKC -/

/-- The equivalence of Stacks Project, Tag 0GKC, from a supplied converse. Let `S` be a scheme
such that every quasi-compact open of `S` has a finite number of irreducible components, let `Λ`
be a Noetherian ring and let `F` be a sheaf of `Λ`-modules on the small étale site of `S`. Then
`F` is a finite type locally constant sheaf of `Λ`-modules if and only if all its stalks at
geometric points are finite, i.e. finitely generated, `Λ`-modules and all specialization maps
between stalks are bijective.

The implication (1) ⟹ (2) is proved here, using neither `hqc` nor the Noetherian hypothesis
on `Λ`; the implication (2) ⟹ (1) is read off from `hconverse`. The converse is proved with no
such argument by `AlgebraicGeometry.isFiniteTypeLocallyConstantModuleSheaf_of_isFG_etaleStalk`,
and the equivalence without `hconverse` is
`AlgebraicGeometry.isFiniteTypeLocallyConstantModuleSheaf_iff_isFG_etaleStalk_and_bijective`. -/
public theorem isFiniteTypeLocallyConstantModuleSheaf_iff_stalks_and_specialization
    [IsNoetherianRing Λ]
    (hqc : ∀ V : S.Opens, IsCompact (V : Set S) → (irreducibleComponents V).Finite)
    (F : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{max (u + 1) r} Λ))
    (hconverse : (∀ V : S.Opens, IsCompact (V : Set S) → (irreducibleComponents V).Finite) →
      (∀ s : GeometricPoint S, ModuleCat.isFG Λ (etaleStalk B S hS s F.obj)) →
      (∀ (s : GeometricPoint S) (σ : GeometricSpecialization B S hS s),
        Function.Bijective (specializationMapOnStalks σ F.obj)) →
      IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
        (SmallEtale.topology B S hS) Λ F) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r} (SmallEtale.topology B S hS) Λ F ↔
      (∀ s : GeometricPoint S, ModuleCat.isFG Λ (etaleStalk B S hS s F.obj)) ∧
        ∀ (s : GeometricPoint S) (σ : GeometricSpecialization B S hS s),
          Function.Bijective (specializationMapOnStalks σ F.obj) := by
  refine ⟨fun hF ↦ ⟨fun s ↦ isFG_etaleStalk_of_isFiniteTypeLocallyConstantModuleSheaf
      B S hS Λ F hF s,
    fun s σ ↦ bijective_specializationMapOnStalks_of_isFiniteTypeLocallyConstantModuleSheaf
      B S hS Λ F hF s σ⟩, ?_⟩
  rintro ⟨hfin, hsp⟩
  exact hconverse hqc hfin hsp

end AlgebraicGeometry

end
