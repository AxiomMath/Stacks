module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatEquivalenceIff
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackFlatInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteUpSheafificationPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseAssociatedModuleTensor
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleFiniteness.Flat
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification
public import StacksFrontier.RingTheory.Flat.FaithfullyFlatRelationDescent
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
import StacksCore.Tactic.StacksAttribute

/-! # Flatness of the associated module on the big `τ`-site

Descent, Lemma 05VG asserts, for each of the properties of Modules on Sites, Definitions 03DE,
03DL and 03ER, that a quasi-coherent `𝒪_S`-module `𝓗` has the property if and only if `𝓗ᵃ` has
it as an `𝒪`-module on `(Sch/S)_τ`.  This file settles the clause of Definition 03ER (3),
*flatness*, at the five big sites `(Sch/S)_τ` for
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}`:

    `𝓗` flat on `S_Zar`  ↔  `𝓗ᵃ` flat on `(Sch/S)_τ`.

That equivalence is `AlgebraicGeometry.BigFppfOver.isFlat_baseAssociatedModule_iff` and carries
the `@[stacks 05VG]` attribute.  The two small sites are settled separately, as
`AlgebraicGeometry.SmallEtale.isFlat_associatedModule_iff` and
`AlgebraicGeometry.SmallZariski.isFlat_iff_associatedModule`.

## The forward half

`𝓗 ↦ 𝓗ᵃ` on the big `τ`-site *is* the pullback of sheaves of modules along the morphism of
ringed topoi of Stacks 070U, which is
`AlgebraicGeometry.BigFppfOver.pullbackModulesIsoBaseAssociatedModule` (Stacks 03D6 (2) at that
morphism).  Modules on Sites, Lemma 05VD says a pullback of a flat module is flat; it is proved
for ringed topoi at six independent universes as
`Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules`, and flatness is carried across the
identification by `Stacks.ModuleUp.isFlat_of_iso_anySite`.

So the forward half needs neither quasi-coherence nor any fact about the coverings of the big
site, and `𝓗` is an arbitrary sheaf of `𝒪_S`-modules in
`AlgebraicGeometry.BigFppfOver.isFlat_baseAssociatedModule_of_isFlat` — the source's clause
carries quasi-coherence, so that is the source's implication over a weaker hypothesis.

The one instance 05VD asks for beyond those already in the library is a left exact sheafification
of `Type`-valued presheaves on the big site.  Mathlib's size-matched instance does not apply —
the objects of `(Sch/S)_τ` lie one universe above its sections — but the site is essentially
small, and `AlgebraicGeometry.BigFppfOver.hasSheafify_type_baseOver` is exactly that statement,
kept as a theorem rather than an instance, as the module docstring of
`StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification` explains.  It is
made a local instance here.

## The converse half

`AlgebraicGeometry.BigFppfOver.isFlat_of_isFlat_baseAssociatedModule` runs through the local
equational criterion, uniformly in `τ`.  Six steps compose, and the only property of `τ` any of
them uses is that a `τ`-covering family is jointly surjective with flat members.

1. Stacks 05NE, `AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat`, reduces flatness of
   `𝓗` to flatness of every stalk `𝓗ₓ` over `𝒪_{S,x}`, and Mathlib's equational criterion
   `Module.Flat.of_forall_isTrivialRelation` reduces that to the triviality of every relation
   `∑ᵢ φᵢ • σᵢ = 0` among germs.
2. A relation among germs is the germ of a relation among sections over one open `U ∋ x`
   (`AlgebraicGeometry.BigFppfOver.exists_relation_over_open`).
3. Read at the object `U → S` of the big site:  the structure ring there is the global functions
   of the open subscheme `U` and the sections of `𝓗ᵃ` are the sections of `U.ι^*𝓗`, so pulling
   a section back carries the relation over
   (`AlgebraicGeometry.BigFppfOver.sum_smul_pullbackSectionHom_eq_zero`).  **This is where
   quasi-coherence enters**, through
   `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSectionsSheaf` (Stacks 03FH (1)):
   only for a quasi-coherent `𝓗` is `𝓗ᵃ` the sheaf of sections `(T → S) ↦ Γ(T, T.hom^*𝓗)`.
4. Stacks 08FC, in the free-universe form
   `Stacks.SheafOfModules.isFlat_iff_hasLocalSingleRelationFactorizations_freeUniverse`, turns
   flatness of `𝓗ᵃ` into a finite free factorization of that relation on a `τ`-covering sieve
   of `U → S`;  `AlgebraicGeometry.BigFppfOver.exists_mem_of_mem_topology` picks out a member
   `T → U` of that sieve whose image contains `x`, with `T → S` flat.
5. At a point `y` of `T` over `x` the stalk map `𝒪_{S,x} → 𝒪_{T,y}` is a flat local
   homomorphism, hence faithfully flat, and the stalk of the pullback is the base change
   (Stacks 0098,
   `AlgebraicGeometry.RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`, whose
   formula sends the germ of a pulled-back section to `1 ⊗ₜ` its germ).  So the relation
   vanishes trivially after the base change to `𝒪_{T,y}`.
6. `Stacks.FlatDescent.vanishesTrivially_of_baseChange` removes the base change:  vanishing
   trivially descends along a faithfully flat ring map, with no hypothesis on the module.

Two other routes to the converse are ruled out, and the counterexamples are formalized.  It is not
available from `Stacks.Sheaves.RingedToposModules.isFlat_of_isFlat_pullbackModules`, whose
hypothesis is that the pullback preserve and reflect monomorphisms: at every big site and every
`τ` the pullback does **not** preserve them, which is
`AlgebraicGeometry.AssociatedModuleNotExact.not_preservesMonomorphisms_baseAssociatedModuleQcoh`
(Descent, Lemma 06VE (6)), with witness multiplication by `2` on `Spec ℤ` read at the object
`Spec 𝔽₂ → Spec ℤ`;  a non-exact pullback can still carry flat modules to flat modules, so this
is no contradiction with 05VG.  Nor is it available from
`Stacks.Sheaves.LocalTypeComparison.isFlat_iff`, which needs the pushforward to be an equivalence
of topoi.  Nor can it be run through points of the big site: `Spec` of a local ring is a point of
the big Zariski site and `Spec` of a strictly henselian local ring one of the big étale and big
smooth sites, but at `τ = syntomic` and `τ = fppf` the points have stalk rings which are fields,
over which flatness is vacuous.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 070U](https://stacks.math.columbia.edu/tag/070U)
* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] hasSheafify_type_baseOver

/-- **The forward half of Descent, Lemma 05VG for Modules on Sites, Definition 03ER (3), at the
big site `(Sch/S)_τ`, for every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.**  If a sheaf of
`𝒪_S`-modules `𝓗` is flat, then `𝓗ᵃ` is flat as an `𝒪`-module on `(Sch/S)_τ`.

This is Modules on Sites, Lemma 05VD —
`Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules`, a pullback of a flat module is
flat — at the morphism of ringed topoi of Stacks 070U, transported along
`AlgebraicGeometry.BigFppfOver.pullbackModulesIsoBaseAssociatedModule`, which identifies the
pullback along it with `𝓗 ↦ 𝓗ᵃ`.

`𝓗` is arbitrary: neither quasi-coherence nor anything about the coverings of the big site
enters, so this is the source's implication over a weaker hypothesis than the source's.

It carries no `@[stacks 05VG]` attribute, being one implication of a clause the source states as
an equivalence; the attribute sits on that equivalence,
`AlgebraicGeometry.BigFppfOver.isFlat_baseAssociatedModule_iff`. -/
public theorem isFlat_baseAssociatedModule_of_isFlat (τ : SiteKind) (𝓗 : S.Modules)
    (h𝓗 : Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓗) :
    Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := (baseRingedSite B S hS τ).O)
      ((baseAssociatedModule B S hS τ).obj 𝓗) := by
  refine Stacks.ModuleUp.isFlat_of_iso_anySite (O := (baseRingedSite B S hS τ).O)
    ((pullbackModulesIsoBaseAssociatedModule B S hS τ).app 𝓗) ?_
  exact Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules
    (baseRingedToposModulesHom B S hS τ) 𝓗 h𝓗

/-! ### The converse half -/

section Converse

variable (τ : SiteKind) (𝓗 : S.Modules) [𝓗.IsQuasicoherent]

/-- The germ of a sum of scalar multiples is the sum of the products of the germs. -/
private lemma germ_sum_smul {X : TopCat.{u}} {R : TopCat.Presheaf CommRingCat.{u} X}
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (x : ↥X)
    (U : Opens ↥X) (hx : x ∈ U) {ι : Type*} [Fintype ι] (a : ι → ToType (R.obj (op U)))
    (s : ι → ToType (M.obj (op U))) :
    TopCat.Presheaf.germ M.presheaf U x hx (∑ i, a i • s i)
      = ∑ i, R.germ U x hx (a i) • TopCat.Presheaf.germ M.presheaf U x hx (s i) :=
  (map_sum (TopCat.Presheaf.germ M.presheaf U x hx).hom (fun i => a i • s i) Finset.univ).trans
    (Finset.sum_congr rfl fun i _ => PresheafOfModules.germ_smul M x U hx (a i) (s i))

/-- **A relation among germs comes from a relation among sections over one open.**  Given
finitely many elements of the stalk of the structure presheaf and of a presheaf of modules over
it at a point `x`, together with a relation between them, there is an open neighbourhood of `x`
carrying sections with those germs which satisfy the same relation.

This is the germ-lifting step of the converse half: Mathlib's equational criterion for flatness
of the stalk asks for a relation among germs to be trivial, and the criterion of Stacks 08FC on
the big site speaks about relations among *sections*. -/
private lemma exists_relation_over_open {X : TopCat.{u}}
    {R : TopCat.Presheaf CommRingCat.{u} X}
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (x : ↥X) {n : ℕ}
    (φ : Fin n → ToType (R.stalk x))
    (σ : Fin n → ToType (TopCat.Presheaf.stalk M.presheaf x))
    (hrel : ∑ i, φ i • σ i = 0) :
    ∃ (U : Opens ↥X) (hx : x ∈ U) (a : Fin n → ToType (R.obj (op U)))
      (s : Fin n → ToType (M.obj (op U))),
      (∀ i, R.germ U x hx (a i) = φ i) ∧
      (∀ i, TopCat.Presheaf.germ M.presheaf U x hx (s i) = σ i) ∧
      ∑ i, a i • s i = 0 := by
  classical
  choose V hV s₀ hs₀ using fun i : Fin n => TopCat.Presheaf.exists_germ_eq M.presheaf (σ i)
  choose W hW a₀ ha₀ using fun i : Fin n => TopCat.Presheaf.exists_germ_eq R (φ i)
  obtain ⟨U₀, hxU₀, hle⟩ := Stacks.SheafOfModules.exists_nbhd_le x
    (fun j : Fin n ⊕ Fin n => j.elim V W)
    (by rintro (i | i) <;> [exact hV i; exact hW i])
  set a₁ : Fin n → ToType (R.obj (op U₀)) := fun i =>
    R.map (homOfLE (hle (Sum.inr i))).op (a₀ i) with ha₁
  set s₁ : Fin n → ToType (M.obj (op U₀)) := fun i =>
    M.restrictₛₗ (homOfLE (hle (Sum.inl i))).op (s₀ i) with hs₁
  have hga : ∀ i, R.germ U₀ x hxU₀ (a₁ i) = φ i := fun i =>
    (TopCat.Presheaf.germ_res_apply R (homOfLE (hle (Sum.inr i))) x hxU₀ (a₀ i)).trans (ha₀ i)
  have hgs : ∀ i, TopCat.Presheaf.germ M.presheaf U₀ x hxU₀ (s₁ i) = σ i := fun i =>
    (TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (hle (Sum.inl i))) x hxU₀
      (s₀ i)).trans (hs₀ i)
  have hz : TopCat.Presheaf.germ M.presheaf U₀ x hxU₀ (∑ i, a₁ i • s₁ i) = 0 :=
    (germ_sum_smul M x U₀ hxU₀ a₁ s₁).trans
      ((Finset.sum_congr rfl fun i _ => by rw [hga i, hgs i]).trans hrel)
  obtain ⟨U, hxU, i₁, i₂, he⟩ := TopCat.Presheaf.germ_eq M.presheaf x hxU₀ hxU₀
    (∑ i, a₁ i • s₁ i) 0
    (hz.trans (map_zero (TopCat.Presheaf.germ M.presheaf U₀ x hxU₀).hom).symm)
  refine ⟨U, hxU, fun i => R.map i₁.op (a₁ i), fun i => M.restrictₛₗ i₁.op (s₁ i), ?_, ?_, ?_⟩
  · exact fun i => (TopCat.Presheaf.germ_res_apply R i₁ x hxU (a₁ i)).trans (hga i)
  · exact fun i => (TopCat.Presheaf.germ_res_apply M.presheaf i₁ x hxU (s₁ i)).trans (hgs i)
  · refine Eq.trans (Eq.symm (Eq.trans (map_sum (M.restrictₛₗ i₁.op)
      (fun i => a₁ i • s₁ i) Finset.univ)
      (Finset.sum_congr rfl fun i _ => (M.restrictₛₗ i₁.op).map_smulₛₗ (a₁ i) (s₁ i)))) ?_
    exact he.trans (map_zero (M.presheaf.map i₂.op).hom)

omit [𝓗.IsQuasicoherent] in
/-- **A relation over an open `U` of `S` pulls back to a relation at the object `U → S` of the
big site.**  Pulling a section of `𝓗` back to the open subscheme `U` is semilinear over
`AlgebraicGeometry.Scheme.Hom.appLE`, so it carries a relation to a relation. -/
private lemma sum_smul_pullbackSectionHom_eq_zero {U : S.Opens}
    (hUle : (⊤ : (Scheme.Opens.toScheme U).Opens) ≤ Scheme.Opens.ι U ⁻¹ᵁ U) {n : ℕ}
    (a : Fin n → Γ(S, U)) (s : Fin n → Γ(𝓗, U)) (hrelU : ∑ i, a i • s i = 0) :
    ∑ i, (Scheme.Hom.appLE (Scheme.Opens.ι U) U ⊤ hUle (a i) :
          ToType
            ((Stacks.SheafOfModules.Tensor.ringSheaf (baseRingedSite B S hS τ).O).obj.obj
              (op (opensObj B S hS U)))) •
        (pullbackSectionHom (Scheme.Opens.ι U) 𝓗 U ⊤ hUle (s i) :
          ToType ((sectionsSheafOfModules B S hS τ 𝓗).val.obj
            (op (opensObj B S hS U)))) = 0 := by
  refine Eq.trans (Eq.symm (Eq.trans
    (map_sum (pullbackSectionHom (Scheme.Opens.ι U) 𝓗 U ⊤ hUle).hom
      (fun i => a i • s i) Finset.univ)
    (Finset.sum_congr rfl fun i _ =>
      pullbackSectionHom_smul (Scheme.Opens.ι U) 𝓗 U ⊤ hUle (a i) (s i)))) ?_
  rw [hrelU]
  exact map_zero (pullbackSectionHom (Scheme.Opens.ι U) 𝓗 U ⊤ hUle).hom

/-- **Restricting a pulled-back section along a morphism of the big site pulls it back further.**
The sections of `𝓗ᵃ` over an object are the sections of the pullback of `𝓗` to it, and its
restriction maps are the pullback maps on sections; this is
`AlgebraicGeometry.pullbackSectionsMap_pullbackSectionHom` read at that identification. -/
private lemma sectionsSheaf_map_pullbackSectionHom {U : S.Opens}
    (hUle : (⊤ : (Scheme.Opens.toScheme U).Opens) ≤ Scheme.Opens.ι U ⁻¹ᵁ U)
    {c : BigFppfOver B S hS} (q : c ⟶ opensObj B S hS U)
    (hcle : (⊤ : ((toScheme B S hS).obj c).Opens) ≤ c.hom.hom ⁻¹ᵁ U) (sec : Γ(𝓗, U)) :
    ((sectionsSheafOfModules B S hS τ 𝓗).val.map q.op).hom
        (pullbackSectionHom (Scheme.Opens.ι U) 𝓗 U ⊤ hUle sec)
      = pullbackSectionHom c.hom.hom 𝓗 U ⊤ hcle sec :=
  pullbackSectionsMap_pullbackSectionHom 𝓗
    ((Over.post (X := B.obj hS) B.inclusion).map q) U hUle hcle sec

/-- **The same statement for the structure sheaf.**  Restricting along `q` the image of a
function on `U` in the global functions of the open subscheme `U` is its image in the global
functions of the source of `q`. -/
private lemma app_top_appLE {U : S.Opens}
    (hUle : (⊤ : (Scheme.Opens.toScheme U).Opens) ≤ Scheme.Opens.ι U ⁻¹ᵁ U)
    {c : BigFppfOver B S hS} (q : c ⟶ opensObj B S hS U)
    (hcle : (⊤ : ((toScheme B S hS).obj c).Opens) ≤ c.hom.hom ⁻¹ᵁ U) (r : Γ(S, U)) :
    ((toScheme B S hS).map q).app ⊤ (Scheme.Hom.appLE (Scheme.Opens.ι U) U ⊤ hUle r)
      = Scheme.Hom.appLE c.hom.hom U ⊤ hcle r := by
  have hcq : c.hom.hom = (toScheme B S hS).map q ≫ Scheme.Opens.ι U := hom_hom_eq B S hS q
  revert hcle
  rw [hcq]
  intro hcle
  have hb : Scheme.Hom.appLE ((toScheme B S hS).map q)
      (⊤ : (Scheme.Opens.toScheme U).Opens) (⊤ : ((toScheme B S hS).obj c).Opens) le_rfl
      = ((toScheme B S hS).map q).app ⊤ :=
    Scheme.Hom.appLE_preimage_self ((toScheme B S hS).map q) ⊤
  rw [← hb]
  exact congrArg
    (fun k : Γ(S, U) ⟶ Γ((toScheme B S hS).obj c, ⊤) => ConcreteCategory.hom k r)
    (Scheme.Hom.appLE_comp_appLE ((toScheme B S hS).map q) (Scheme.Opens.ι U) U ⊤ ⊤ hUle le_rfl)

omit [𝓗.IsQuasicoherent] in
/-- **Faithfully flat descent of a factorization, read at a point.**  Let `g : T ⟶ S` be flat,
`y` a point of `T` and `U` an open of `S` containing its image and containing the whole of `T`.
A relation among sections of `𝓗` over `U` whose pullback to `T` admits a finite free
factorization already vanishes trivially at the stalk at `g y`. -/
private lemma vanishesTrivially_of_factorization {T : Scheme.{u}} (g : T ⟶ S) [Flat g] (y : ↥T)
    {U : S.Opens} (hxU : g.base y ∈ U) (hgle : (⊤ : T.Opens) ≤ g ⁻¹ᵁ U)
    {l : ℕ} (a : Fin l → Γ(S, U)) (s : Fin l → Γ(𝓗, U))
    (φ : Fin l → ToType (S.presheaf.stalk (g.base y)))
    (σ : Fin l → ToType (TopCat.Presheaf.stalk 𝓗.val.presheaf (g.base y)))
    (hga : ∀ i, S.presheaf.germ U (g.base y) hxU (a i) = φ i)
    (hgs : ∀ i, TopCat.Presheaf.germ 𝓗.val.presheaf U (g.base y) hxU (s i) = σ i)
    {k : ℕ} (t : Fin k → Γ((Scheme.Modules.pullback g).obj 𝓗, ⊤))
    (Bm : Fin k → Fin l → Γ(T, ⊤))
    (h1 : ∀ i, pullbackSectionHom g 𝓗 U ⊤ hgle (s i) = ∑ κ, Bm κ i • t κ)
    (h2 : ∀ κ, ∑ i, Bm κ i * Scheme.Hom.appLE g U ⊤ hgle (a i) = 0) :
    TensorProduct.VanishesTrivially (ToType (S.presheaf.stalk (g.base y))) φ σ := by
  classical
  let : Algebra (S.presheaf.stalk (g.base y)) (T.presheaf.stalk y) :=
    (g.stalkMap y).hom.toAlgebra
  have : IsLocalHom (algebraMap (S.presheaf.stalk (g.base y)) (T.presheaf.stalk y)) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  have : Module.Flat (S.presheaf.stalk (g.base y)) (T.presheaf.stalk y) := Flat.stalkMap g y
  have : Module.FaithfullyFlat (S.presheaf.stalk (g.base y)) (T.presheaf.stalk y) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨e₀, he₀⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    g.toLRSHom.toShHom 𝓗 y
  let e : ToType (TopCat.Presheaf.stalk ((Scheme.Modules.pullback g).obj 𝓗).val.presheaf y)
      ≃ₗ[T.presheaf.stalk y]
      TensorProduct (S.presheaf.stalk (g.base y)) (T.presheaf.stalk y)
        (ToType (TopCat.Presheaf.stalk 𝓗.val.presheaf (g.base y))) := e₀
  have he : ∀ (V : S.Opens) (hv : g.base y ∈ V) (hvle : (⊤ : T.Opens) ≤ g ⁻¹ᵁ V)
      (tt : Γ(𝓗, V)),
      e (TopCat.Presheaf.germ ((Scheme.Modules.pullback g).obj 𝓗).val.presheaf ⊤ y trivial
          (pullbackSectionHom g 𝓗 V ⊤ hvle tt))
        = (1 : T.presheaf.stalk y) ⊗ₜ
            TopCat.Presheaf.germ 𝓗.val.presheaf V (g.base y) hv tt := fun V hv hvle tt =>
    (congrArg e (TopCat.Presheaf.germ_res_apply _ (homOfLE hvle) y trivial _)).trans
      (he₀ V hv tt)
  refine Stacks.FlatDescent.vanishesTrivially_of_baseChange (B := T.presheaf.stalk y) ?_
  refine TensorProduct.VanishesTrivially.of_fintype
    (fun i κ => T.presheaf.germ ⊤ y trivial (Bm κ i))
    (fun κ => e (TopCat.Presheaf.germ ((Scheme.Modules.pullback g).obj 𝓗).val.presheaf
      ⊤ y trivial (t κ))) ?_ ?_
  · intro i
    calc (1 : T.presheaf.stalk y) ⊗ₜ σ i
        = e (TopCat.Presheaf.germ ((Scheme.Modules.pullback g).obj 𝓗).val.presheaf ⊤ y trivial
            (pullbackSectionHom g 𝓗 U ⊤ hgle (s i))) := by
          rw [← hgs i]
          exact (he U hxU hgle (s i)).symm
      _ = e (TopCat.Presheaf.germ ((Scheme.Modules.pullback g).obj 𝓗).val.presheaf ⊤ y trivial
            (∑ κ, Bm κ i • t κ)) :=
          congrArg (fun z => e (TopCat.Presheaf.germ
            ((Scheme.Modules.pullback g).obj 𝓗).val.presheaf ⊤ y trivial z)) (h1 i)
      _ = ∑ κ, T.presheaf.germ ⊤ y trivial (Bm κ i) •
            e (TopCat.Presheaf.germ ((Scheme.Modules.pullback g).obj 𝓗).val.presheaf
              ⊤ y trivial (t κ)) := by
          refine (congrArg e (germ_sum_smul (R := T.presheaf)
            ((Scheme.Modules.pullback g).obj 𝓗).val y ⊤ trivial (fun κ => Bm κ i) t)).trans ?_
          exact (map_sum e _ _).trans (Finset.sum_congr rfl fun κ _ => e.map_smul _ _)
  · intro κ
    have hgr : ∀ i, T.presheaf.germ ⊤ y trivial (Scheme.Hom.appLE g U ⊤ hgle (a i))
        = algebraMap (S.presheaf.stalk (g.base y)) (T.presheaf.stalk y) (φ i) := fun i => by
      rw [RingHom.algebraMap_toAlgebra, ← hga i]
      exact (TopCat.Presheaf.germ_res_apply T.presheaf (homOfLE hgle) y trivial _).trans
        (Scheme.Hom.germ_stalkMap_apply g U y hxU (a i)).symm
    calc ∑ i, T.presheaf.germ ⊤ y trivial (Bm κ i) •
            algebraMap (S.presheaf.stalk (g.base y)) (T.presheaf.stalk y) (φ i)
        = T.presheaf.germ ⊤ y trivial (∑ i, Bm κ i * Scheme.Hom.appLE g U ⊤ hgle (a i)) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hgr i, smul_eq_mul]
      _ = 0 := by rw [h2 κ, map_zero]

/-- **Every relation at a stalk of `𝓗` vanishes trivially, if `𝓗ᵃ` is flat.**  This is the
whole of the converse half: Stacks 08FC at the big site turns flatness of `𝓗ᵃ` into a local
factorization of the relation read at the object `U → S`,
`AlgebraicGeometry.BigFppfOver.exists_mem_of_mem_topology` extracts from the covering sieve a
member through which the point factors, and
`AlgebraicGeometry.BigFppfOver.vanishesTrivially_of_factorization` descends the factorization
back to the stalk. -/
private lemma vanishesTrivially_stalk (x : ↥S)
    (hflat : Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (baseRingedSite B S hS τ).O) ((baseAssociatedModule B S hS τ).obj 𝓗))
    {l : ℕ} (φ : Fin l → ToType (S.presheaf.stalk x))
    (σ : Fin l → ToType (TopCat.Presheaf.stalk 𝓗.val.presheaf x))
    (hrel : ∑ i, φ i • σ i = 0) :
    TensorProduct.VanishesTrivially (ToType (S.presheaf.stalk x)) φ σ := by
  classical
  have hflat' : Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (baseRingedSite B S hS τ).O) (sectionsSheafOfModules B S hS τ 𝓗) :=
    Stacks.ModuleUp.isFlat_of_iso_anySite (O := (baseRingedSite B S hS τ).O)
      (baseAssociatedModuleIsoSectionsSheaf B S hS τ 𝓗) hflat
  have H := (Stacks.SheafOfModules.isFlat_iff_hasLocalSingleRelationFactorizations_freeUniverse
    (baseRingedSite B S hS τ).O (sectionsSheafOfModules B S hS τ 𝓗)).1 hflat'
  obtain ⟨U, hxU, a, s, hga, hgs, hrelU⟩ :=
    exists_relation_over_open (X := S) (R := S.presheaf) 𝓗.val x φ σ hrel
  have hUle : (⊤ : (Scheme.Opens.toScheme U).Opens) ≤ Scheme.Opens.ι U ⁻¹ᵁ U :=
    Scheme.Opens.top_le_ι_preimage (le_refl U)
  obtain ⟨Rv, hRv, hfac⟩ := H (opensObj B S hS U) l
    (fun i => Scheme.Hom.appLE (Scheme.Opens.ι U) U ⊤ hUle (a i))
    (fun i => pullbackSectionHom (Scheme.Opens.ι U) 𝓗 U ⊤ hUle (s i))
    (sum_smul_pullbackSectionHom_eq_zero S 𝓗 hUle a s hrelU)
  obtain ⟨c, q, hq, hflatq, -, hmem⟩ := exists_mem_of_mem_topology B S hS
    (baseOverTopology_le_fppf B S hS τ _ hRv) (⟨x, hxU⟩ : ↥(Scheme.Opens.toScheme U))
  obtain ⟨y, hy⟩ := hmem
  have hcq : c.hom.hom = (toScheme B S hS).map q ≫ Scheme.Opens.ι U := hom_hom_eq B S hS q
  have hcle : (⊤ : ((toScheme B S hS).obj c).Opens) ≤ c.hom.hom ⁻¹ᵁ U := by
    rw [hcq]
    exact fun z _ => hUle trivial
  have hyx : c.hom.hom.base y = x := by
    rw [hcq]
    exact congrArg (fun w => (Scheme.Opens.ι U).base w) hy
  have : Flat ((toScheme B S hS).map q) := hflatq
  have : Flat c.hom.hom := by
    rw [hcq]
    infer_instance
  obtain ⟨k, t, Bm, hfac1, hfac2⟩ := hfac q hq
  subst hyx
  refine vanishesTrivially_of_factorization S 𝓗 c.hom.hom y hxU hcle a s φ σ hga hgs
    t Bm (fun i => ?_) (fun κ => ?_)
  · exact (sectionsSheaf_map_pullbackSectionHom B S hS τ 𝓗 hUle q hcle (s i)).symm.trans
      (hfac1 i)
  · refine Eq.trans ?_ (hfac2 κ 0)
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrArg _ (app_top_appLE B S hS hUle q hcle (a i)).symm

/-- **The converse half of Descent, Lemma 05VG for Modules on Sites, Definition 03ER (3), at the
big site `(Sch/S)_τ`, for every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.**  If `𝓗ᵃ` is
flat as an `𝒪`-module on `(Sch/S)_τ` then the quasi-coherent `𝒪_S`-module `𝓗` is flat.

The route is `τ`-uniform and uses nothing about `τ` beyond the fact that a covering family is
jointly surjective with flat members.  Stacks 05NE,
`AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat`, reduces flatness of `𝓗` to flatness of
each stalk; Mathlib's equational criterion reduces that to the triviality of every relation among
germs, which is
`AlgebraicGeometry.BigFppfOver.vanishesTrivially_stalk`. -/
public theorem isFlat_of_isFlat_baseAssociatedModule
    (hflat : Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (baseRingedSite B S hS τ).O) ((baseAssociatedModule B S hS τ).obj 𝓗)) :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓗 := by
  have key : ∀ x : ↥S, Module.Flat (ToType (S.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk 𝓗.val.presheaf x)) := fun x =>
    Module.Flat.of_forall_isTrivialRelation fun {_} {φ} {σ} hrel =>
      Module.isTrivialRelation_iff_vanishesTrivially.2
        (vanishesTrivially_stalk B S hS τ 𝓗 x hflat φ σ hrel)
  exact (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat S.sheaf 𝓗).2 key

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03ER (3), at the big site
`(Sch/S)_τ`, for every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.**  A quasi-coherent
`𝒪_S`-module `𝓗` is flat if and only if `𝓗ᵃ` is flat as an `𝒪`-module on `(Sch/S)_τ`.

The `only if` half is `AlgebraicGeometry.BigFppfOver.isFlat_baseAssociatedModule_of_isFlat`,
which needs neither quasi-coherence nor anything about the coverings of the big site; the `if`
half is `AlgebraicGeometry.BigFppfOver.isFlat_of_isFlat_baseAssociatedModule`, and that is where
the source's quasi-coherence hypothesis is used — the sections of `𝓗ᵃ` at an object `T → S` are
the sections of the pullback of `𝓗` to `T` only for a quasi-coherent `𝓗`. -/
@[stacks 05VG "flat (03ER (3)), big site (Sch/S)_τ at every τ, at the comparison functor of \
03DX itself"]
public theorem isFlat_baseAssociatedModule_iff :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓗 ↔
      Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := (baseRingedSite B S hS τ).O)
        ((baseAssociatedModule B S hS τ).obj 𝓗) :=
  ⟨isFlat_baseAssociatedModule_of_isFlat B S hS τ 𝓗,
    isFlat_of_isFlat_baseAssociatedModule B S hS τ 𝓗⟩

end Converse

end AlgebraicGeometry.BigFppfOver

end
