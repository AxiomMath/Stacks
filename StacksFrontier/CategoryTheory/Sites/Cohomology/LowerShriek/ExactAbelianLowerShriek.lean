module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriek
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.AdjointAcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.CategoryTheory.Sites.GrothendieckAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtendScalarsAdjunction

/-!
# The derived lower shriek of modules when lower shriek of abelian sheaves is exact

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, let `g : Sh(C) ⟶ Sh(D)` be
the corresponding morphism of topoi, let `O_D` be a sheaf of rings on `D` and set
`O_C = g^{-1} O_D`. Stacks 07AC asserts that `g_! : Mod(O_C) ⥤ Mod(O_D)` has a left derived
functor `Lg_!`. The source runs the criterion of Stacks 0794 with the class of direct sums of the
`j_{U!} O_U`, and the one non-formal input is that `g_!` carries a bounded above acyclic complex
of such direct sums to an acyclic complex; that is reduced to the vanishing
`Ext^p_{O_C}(j_{U!} O_U, g^{-1} I) = 0` for `p > 0` and `I` an injective `O_D`-module.

This file proves that vanishing, and with it the existence and the absoluteness of `Lg_!`, in
the case where `g_!` is *exact on abelian sheaves* — the case of the inclusion of the small
étale site of a scheme into its big étale site, where `g_!` is the inverse image `π_S^{-1}` of a
morphism of topoi. Under that hypothesis the vanishing needs no Čech cohomology: writing
`λ` for the exact left adjoint of `g^{-1}` on abelian sheaves and `X` for a sectionwise
torsion-free abelian sheaf on `C`,

`Ext^p_{O_C}(O_C ⊗ X, g^{-1} I) = Ext^p_{Ab(C)}(X, g^{-1} I) = Ext^p_{Ab(D)}(λ X, I) = 0`,

the first identification by Stacks 03FD (an injective module is `Ext`-acyclic against a
torsion-free abelian sheaf), the second because `g^{-1}` is exact with an exact left adjoint, and
the vanishing because `λ X` is again torsion-free, `λ` being exact and additive. Every module is
a quotient of an `O_C ⊗ X` of this kind, `X` the sheafified free abelian presheaf on its sections.

## Main definitions

* `Stacks.Cohomology.ExactAbelianLowerShriek.freeCover`: the free cover `O ⊗_ℤ ℤ[M]` of a sheaf of
  modules `M`, with its epimorphism `Stacks.Cohomology.ExactAbelianLowerShriek.freeCoverπ`
  onto `M`.

## Main results

* `CategoryTheory.Adjunction.extAcyclic_of_corepresentation`: the abstract form of the chain of
  identifications above.
* `CategoryTheory.epi_of_corepresentation`: a morphism out of an object corepresenting
  `Hom(X, Φ -)` along a faithful `Φ` is an epimorphism when the morphism it names out of `X` is.
* `Stacks.Cohomology.ExactAbelianLowerShriek.exists_epi_extAcyclic`: every `O_C`-module is a
  quotient of an object which is `Ext`-acyclic for `g_! ⊣ g^*`.
* `Stacks.Cohomology.ExactAbelianLowerShriek.map_acyclic`: `g_!`, and `g_!` followed by any exact
  functor, carries a bounded above acyclic complex of `Ext`-acyclic objects to an acyclic complex.
* `Stacks.Cohomology.ExactAbelianLowerShriek.hasPointwiseLeftDerivedFunctor`:
  **Stacks 07AC, existence**, when `g_!` is exact on abelian sheaves.
* `Stacks.Cohomology.ExactAbelianLowerShriek.isLeftDerivedFunctor_comp`: the resulting `Lg_!`
  stays a left derived functor after composition with any functor.

## Implementation notes

The class with which Stacks 0794 is run is the class of all objects that are `Ext`-acyclic for
the adjunction `g_! ⊣ g^*`, rather than the direct sums of the `j_{U!} O_U`: it contains zero,
is closed under direct sums, and contains a quotient presentation of every module, which is all
the criterion asks. The generators are the free covers `O ⊗_ℤ ℤ[M]`, whose underlying
torsion-free abelian sheaf `ℤ[M]` is what Stacks 03FD needs, instead of the `j_{U!} O_U`: those
are built from the unit module, which exists only when the module universe is the ring
universe. The ring universe `r` and the module universe `max u v r t` are independent, as they
must be for the étale sites of a scheme, whose structure rings are one universe below their
modules; the abelian-category facts about the four categories involved (Grothendieck
abelianness, enough injectives, `Ext` in the module universe, exactness of `ℕ`-indexed
colimits) are derived inside the proofs from Grothendieck abelianness.

The two adjunctions are arbitrary: `F ⊣ G` need not be the lower shriek of Stacks 0797, only an
adjunction whose right adjoint lies over a functor `Gab` of abelian sheaves with an exact left
adjoint. This is what lets the same class serve for a functor that is `F` followed by an exact
functor, which is how the derived small étale pullback is obtained from `Lπ_S^*`.

## References

* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory

section Abstract

universe v u₁ u₂ u₃ u₄

namespace Adjunction

variable {MC : Type u₁} [Category.{v} MC] [Abelian MC] [HasExt.{v} MC] [EnoughInjectives MC]
  {MD : Type u₂} [Category.{v} MD] [Abelian MD] [EnoughInjectives MD]
  {AC : Type u₃} [Category.{v} AC] [Abelian AC] [HasExt.{v} AC]
  {AD : Type u₄} [Category.{v} AD] [Abelian AD] [HasExt.{v} AD] [EnoughInjectives AD]
  {F : MC ⥤ MD} {G : MD ⥤ MC}

/-- **`Ext`-acyclicity for an adjunction from a corepresentation.** Let `F ⊣ G` be an
adjunction between abelian categories, let `ΦC` and `ΦD` be exact functors to further abelian
categories, and let `G` lie over an exact functor `Gab` with an exact left adjoint `L`, in the
sense that `G ⋙ ΦC ≅ ΦD ⋙ Gab`. If `P` corepresents `Hom(X, ΦC -)`, if `ΦC` carries injectives
to objects with no positive `Ext` out of `X`, and if `ΦD` carries injectives to objects with no
positive `Ext` out of `L X`, then `P` is `Ext`-acyclic for `F ⊣ G`:

`Ext^n(P, G I) = Ext^n(X, ΦC (G I)) = Ext^n(X, Gab (ΦD I)) = Ext^n(L X, ΦD I) = 0`.

The first and third identifications are `ModuleSheafCohomology.extComparisonIso`, the third
because `Gab`, a right adjoint of a functor preserving monomorphisms, preserves injectives. -/
theorem extAcyclic_of_corepresentation (adj : F ⊣ G)
    (ΦC : MC ⥤ AC) [ΦC.Additive] [PreservesFiniteLimits ΦC] [PreservesFiniteColimits ΦC]
    (ΦD : MD ⥤ AD) (Gab : AD ⥤ AC) [Gab.Additive] [PreservesFiniteLimits Gab]
    [PreservesFiniteColimits Gab]
    (e : G ⋙ ΦC ≅ ΦD ⋙ Gab)
    {L : AC ⥤ AD} (adjab : L ⊣ Gab) [L.Additive] [L.PreservesMonomorphisms]
    (P : MC) (X : AC)
    (eP : preadditiveCoyoneda.obj (Opposite.op P) ≅
      ΦC ⋙ preadditiveCoyoneda.obj (Opposite.op X))
    (hX : ∀ (I : MC) [Injective I] (n : ℕ) (x : Ext X (ΦC.obj I) (n + 1)), x = 0)
    (hLX : ∀ (I : MD) [Injective I] (n : ℕ) (x : Ext (L.obj X) (ΦD.obj I) (n + 1)), x = 0) :
    adj.extAcyclic P := by
  intro I hI n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e₁ := (ModuleSheafCohomology.extComparisonIso ΦC X P hX eP (m + 1)).app (G.obj I)
  have e₃ := (ModuleSheafCohomology.extComparisonIso Gab X (L.obj X)
    (fun J _ k x => by
      have : Injective (Gab.obj J) := Injective.injective_of_adjoint adjab J
      exact Ext.eq_zero_of_injective x)
    (Stacks.Cohomology.ObjectSections.coyonedaAdjunctionIso adjab X).symm
      (m + 1)).app (ΦD.obj I)
  exact (e₁ ≪≫ (extFunctorObj X (m + 1)).mapIso (e.app I) ≪≫
    e₃.symm).addCommGroupIsoToAddEquiv.subsingleton_congr.mpr
      ⟨fun a b => by rw [hLX I m a, hLX I m b]⟩

omit [HasExt.{v} AC] [HasExt.{v} AD] [EnoughInjectives AD] in
/-- The `Ext`-acyclic class of an adjunction is closed under binary direct sums. -/
theorem extAcyclic_biprod (adj : F ⊣ G) {X Y : MC} (hX : adj.extAcyclic X)
    (hY : adj.extAcyclic Y) : adj.extAcyclic (X ⊞ Y) :=
  adj.extAcyclic_of_iso (biprod.isoCoprod X Y).symm
    (adj.extAcyclic_coproduct (pairFunction X Y) (fun j => by cases j <;> assumption))

omit [HasExt.{v} AC] [HasExt.{v} AD] [EnoughInjectives AD] [EnoughInjectives MC] in
/-- The `Ext`-acyclic class of an adjunction contains a zero object. -/
instance containsZero_extAcyclic (adj : F ⊣ G) : (adj.extAcyclic).ContainsZero :=
  ⟨_, isZero_zero MC, adj.extAcyclic_of_isZero (isZero_zero MC)⟩

end Adjunction

variable {M : Type u₁} [Category.{v} M] [Preadditive M] {A : Type u₂} [Category.{v} A]
  [Preadditive A]

/-- **A corepresenting object maps epimorphically when the morphism it names does.** If `P`
corepresents `Hom(X, Φ -)` along a faithful functor `Φ`, then the morphism `P ⟶ N` corresponding
to an epimorphism `X ⟶ Φ N` is an epimorphism. -/
theorem epi_of_corepresentation (Φ : M ⥤ A) [Φ.Faithful] {P : M} {X : A}
    (eP : preadditiveCoyoneda.obj (Opposite.op P) ≅ Φ ⋙ preadditiveCoyoneda.obj (Opposite.op X))
    {N : M} (x : X ⟶ Φ.obj N) [Epi x] : Epi ((eP.inv.app N) x) := by
  refine ⟨fun {Z} f g h => Φ.map_injective ?_⟩
  rw [← cancel_epi x]
  have key : ∀ k : N ⟶ Z, eP.inv.app Z (x ≫ Φ.map k) = (eP.inv.app N) x ≫ k := fun k =>
    ConcreteCategory.congr_hom (eP.inv.naturality k) x
  apply (eP.app Z).symm.addCommGroupIsoToAddEquiv.injective
  show eP.inv.app Z (x ≫ Φ.map f) = eP.inv.app Z (x ≫ Φ.map g)
  rw [key, key, h]

end Abstract

end CategoryTheory

namespace Stacks.Cohomology.ExactAbelianLowerShriek

section TorsionFree

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasSheafify J Ab.{w}]

/-- An abelian sheaf is sectionwise torsion-free as soon as multiplication by every nonzero
integer is a monomorphism of sheaves. -/
lemma isTorsionFree_of_mono_zsmul {F : Sheaf J Ab.{w}}
    (h : ∀ n : ℤ, n ≠ 0 → Mono (n • 𝟙 F)) (U : Cᵒᵖ) :
    Module.IsTorsionFree ℤ (F.obj.obj U) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro n x hx
  by_cases hn : n = 0
  · exact Or.inl hn
  right
  have := h n hn
  refine (AddCommGrpCat.mono_iff_injective ((n • 𝟙 F).hom.app U)).mp inferInstance ?_
  show (n • 𝟙 F).hom.app U x = (n • 𝟙 F).hom.app U 0
  rw [map_zero]
  exact hx

/-- Multiplication by a nonzero integer is a monomorphism of a sectionwise torsion-free abelian
sheaf. -/
lemma mono_zsmul_of_isTorsionFree {F : Sheaf J Ab.{w}}
    (h : ∀ U, Module.IsTorsionFree ℤ (F.obj.obj U)) (n : ℤ) (hn : n ≠ 0) :
    Mono (n • 𝟙 F) := by
  have (U : Cᵒᵖ) : Mono ((n • 𝟙 F).hom.app U) := by
    have := h U
    rw [AddCommGrpCat.mono_iff_injective]
    exact IsSMulRegular.of_ne_zero hn
  have : Mono (n • 𝟙 F).hom := NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf J Ab.{w}).mono_of_mono_map this

/-- An additive functor of abelian sheaves preserving monomorphisms preserves sectionwise
torsion-freeness. -/
lemma isTorsionFree_map {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [HasSheafify K Ab.{w}] (L : Sheaf J Ab.{w} ⥤ Sheaf K Ab.{w}) [L.Additive]
    [L.PreservesMonomorphisms] {F : Sheaf J Ab.{w}}
    (h : ∀ U, Module.IsTorsionFree ℤ (F.obj.obj U)) (U : Dᵒᵖ) :
    Module.IsTorsionFree ℤ ((L.obj F).obj.obj U) := by
  refine isTorsionFree_of_mono_zsmul (fun n hn => ?_) U
  have := mono_zsmul_of_isTorsionFree h n hn
  have hL : Mono (L.map (n • 𝟙 F)) := inferInstance
  rwa [Functor.map_zsmul, CategoryTheory.Functor.map_id] at hL

end TorsionFree

section FreeSections

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasSheafify J Ab.{w}]

/-- The free abelian presheaf on the underlying presheaf of sets of an abelian sheaf. -/
abbrev freeSectionsPresheaf (F : Sheaf J Ab.{w}) : Cᵒᵖ ⥤ Ab.{w} :=
  F.obj ⋙ forget Ab.{w} ⋙ AddCommGrpCat.free

/-- The sheafified free abelian presheaf on the sections of an abelian sheaf. It is sectionwise
torsion-free (`freeSectionsSheaf_isTorsionFree`) and maps epimorphically onto the sheaf
(`freeSectionsSheafπ`). -/
abbrev freeSectionsSheaf (F : Sheaf J Ab.{w}) : Sheaf J Ab.{w} :=
  (presheafToSheaf J Ab.{w}).obj (freeSectionsPresheaf J F)

/-- The map from the free abelian presheaf on the sections of a presheaf to the presheaf,
sending a generator to the section it names. -/
def freeSectionsPresheafπ (F : Sheaf J Ab.{w}) : freeSectionsPresheaf J F ⟶ F.obj where
  app X := AddCommGrpCat.ofHom (FreeAbelianGroup.lift (fun x : F.obj.obj X => x))
  naturality _ _ f := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro x
    change FreeAbelianGroup.lift (fun x => x)
        (FreeAbelianGroup.map (F.obj.map f) (FreeAbelianGroup.of x)) =
      F.obj.map f (FreeAbelianGroup.lift (fun x => x) (FreeAbelianGroup.of x))
    simp

/-- The map `freeSectionsPresheafπ` is an epimorphism of presheaves. -/
instance (F : Sheaf J Ab.{w}) : Epi (freeSectionsPresheafπ J F) := by
  have (X : Cᵒᵖ) : Epi ((freeSectionsPresheafπ J F).app X) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro x
    exact ⟨FreeAbelianGroup.of x, FreeAbelianGroup.lift_apply_of _ x⟩
  exact NatTrans.epi_of_epi_app _

/-- The canonical epimorphism from the sheafified free abelian presheaf on the sections of an
abelian sheaf onto the sheaf. -/
def freeSectionsSheafπ (F : Sheaf J Ab.{w}) : freeSectionsSheaf J F ⟶ F :=
  (presheafToSheaf J Ab.{w}).map (freeSectionsPresheafπ J F) ≫
    (sheafificationAdjunction J Ab.{w}).counit.app F

/-- The map `freeSectionsSheafπ` is an epimorphism of sheaves. -/
instance (F : Sheaf J Ab.{w}) : Epi (freeSectionsSheafπ J F) := by
  dsimp only [freeSectionsSheafπ]
  infer_instance

/-- The sections of `freeSectionsSheaf J F` over every object are torsion-free abelian groups. -/
lemma freeSectionsSheaf_isTorsionFree (F : Sheaf J Ab.{w}) (U : Cᵒᵖ) :
    Module.IsTorsionFree ℤ ((freeSectionsSheaf J F).obj.obj U) :=
  ModuleSheafCohomology.isTorsionFree_sheafify J (freeSectionsPresheaf J F) (fun V => by
    show Module.IsTorsionFree ℤ (FreeAbelianGroup (F.obj.obj V))
    exact Module.Flat.isTorsionFree) U

end FreeSections

section FreeCover

universe t r v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J Ab.{max r t}] [J.WEqualsLocallyBijective Ab.{max r t}]
  (R : Sheaf J RingCat.{r})

/-- The free cover of a sheaf of modules: `R ⊗_ℤ X` sheafified, for `X` the free abelian
presheaf on the sections of the underlying abelian sheaf. -/
abbrev freeCover (M : SheafOfModules.{max r t} R) : SheafOfModules.{max r t} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    (Stacks.SheafOfModules.tensorPresheaf R.obj
      (freeSectionsPresheaf J ((SheafOfModules.toSheaf R).obj M)))

/-- Morphisms out of the free cover are morphisms out of `freeSectionsSheaf` into the underlying
abelian sheaf. -/
def freeCoverCorepresentation (M : SheafOfModules.{max r t} R) :
    preadditiveCoyoneda.obj (Opposite.op (freeCover J R M)) ≅
      SheafOfModules.toSheaf R ⋙ preadditiveCoyoneda.obj
        (Opposite.op (freeSectionsSheaf J ((SheafOfModules.toSheaf R).obj M))) :=
  Stacks.SheafOfModules.tensorSheafHomIso J R _

/-- The canonical epimorphism from the free cover of a sheaf of modules onto it. -/
def freeCoverπ (M : SheafOfModules.{max r t} R) : freeCover J R M ⟶ M :=
  ((freeCoverCorepresentation J R M).inv.app M)
    (freeSectionsSheafπ J ((SheafOfModules.toSheaf R).obj M))

/-- The map `freeCoverπ` is an epimorphism of sheaves of modules. -/
instance (M : SheafOfModules.{max r t} R) : Epi (freeCoverπ J R M) :=
  epi_of_corepresentation (SheafOfModules.toSheaf R) (freeCoverCorepresentation J R M) _

end FreeCover

section LowerShriek

universe t r v u

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
  [HasSheafify J Ab.{max u v r t}] [J.WEqualsLocallyBijective Ab.{max u v r t}]
  [HasSheafify K Ab.{max u v r t}] [K.WEqualsLocallyBijective Ab.{max u v r t}]
  {R : Sheaf J RingCat.{r}} {O : Sheaf K RingCat.{r}}
  {F : SheafOfModules.{max u v r t} R ⥤ SheafOfModules.{max u v r t} O}
  {G : SheafOfModules.{max u v r t} O ⥤ SheafOfModules.{max u v r t} R}
  (adj : F ⊣ G)
  (Gab : Sheaf K Ab.{max u v r t} ⥤ Sheaf J Ab.{max u v r t}) [Gab.Additive]
  [PreservesFiniteLimits Gab] [PreservesFiniteColimits Gab]
  (e : G ⋙ SheafOfModules.toSheaf R ≅ SheafOfModules.toSheaf O ⋙ Gab)
  {L : Sheaf J Ab.{max u v r t} ⥤ Sheaf K Ab.{max u v r t}} (adjab : L ⊣ Gab)
  [L.PreservesMonomorphisms]

include adj e adjab in
/-- **Every module is a quotient of an `Ext`-acyclic one**, for an adjunction `F ⊣ G` of sheaves
of modules whose right adjoint lies over a functor `Gab` of abelian sheaves with an exact left
adjoint: the free cover `Stacks.Cohomology.ExactAbelianLowerShriek.freeCover` is `Ext`-acyclic, by
`CategoryTheory.Adjunction.extAcyclic_of_corepresentation` and Stacks 03FD for the two sectionwise
torsion-free abelian sheaves that occur. -/
theorem exists_epi_extAcyclic [HasExt.{max u v r t} (SheafOfModules.{max u v r t} R)]
    (M : SheafOfModules.{max u v r t} R) :
    ∃ (P : SheafOfModules.{max u v r t} R) (_ : adj.extAcyclic P) (p : P ⟶ M), Epi p := by
  let := Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, r, t} J R
  let := Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, r, t} K O
  let := Sheaf.isGrothendieckAbelian_of_essentiallySmall_of_hasSheafify.{max u v r t,
    max u v r t, v, max u v r t + 1, u} J Ab.{max u v r t}
  let := Sheaf.isGrothendieckAbelian_of_essentiallySmall_of_hasSheafify.{max u v r t,
    max u v r t, v, max u v r t + 1, u} K Ab.{max u v r t}
  let : HasExt.{max u v r t} (Sheaf J Ab.{max u v r t}) :=
    hasExt_of_enoughInjectives.{max u v r t} _
  let : HasExt.{max u v r t} (Sheaf K Ab.{max u v r t}) :=
    hasExt_of_enoughInjectives.{max u v r t} _
  have := Stacks.SheafOfModules.toSheaf_preservesFiniteColimits R
  have : L.Additive := adjab.left_adjoint_additive
  have hX := freeSectionsSheaf_isTorsionFree J ((SheafOfModules.toSheaf R).obj M)
  have hLX := isTorsionFree_map L hX
  have h₁ : ∀ (I : SheafOfModules.{max u v r t} R) [Injective I] (n : ℕ)
      (x : Ext (freeSectionsSheaf J ((SheafOfModules.toSheaf R).obj M))
        ((SheafOfModules.toSheaf R).obj I) (n + 1)), x = 0 :=
    fun I _ n x =>
      Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree.{max u v r t, max u v t, r, v, u}
      J R I _ hX n x
  have h₂ : ∀ (I : SheafOfModules.{max u v r t} O) [Injective I] (n : ℕ)
      (x : Ext (L.obj (freeSectionsSheaf J ((SheafOfModules.toSheaf R).obj M)))
        ((SheafOfModules.toSheaf O).obj I) (n + 1)), x = 0 :=
    fun I _ n x =>
      Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree.{max u v r t, max u v t, r, v, u}
      K O I _ hLX n x
  exact ⟨freeCover.{max u v t} J R M,
    adj.extAcyclic_of_corepresentation (SheafOfModules.toSheaf R)
      (SheafOfModules.toSheaf O) Gab e adjab _ _ (freeCoverCorepresentation.{max u v t} J R M)
      h₁ h₂, freeCoverπ.{max u v t} J R M, inferInstance⟩

variable {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B] [HasColimitsOfShape ℕ B]
  [HasExactColimitsOfShape ℕ B] (F' : SheafOfModules.{max u v r t} R ⥤ B) [F'.Additive]
  [PreservesFiniteColimits F'] [PreservesColimitsOfShape ℕ F']
  (H : SheafOfModules.{max u v r t} O ⥤ B) [H.Additive] [PreservesFiniteLimits H]
  [PreservesFiniteColimits H] (eF : F' ≅ F ⋙ H)

include adj e adjab eF in
/-- The acyclicity input of Stacks 0794 for any functor `F'` which is `F` followed by an exact
functor: `F'` carries a bounded above acyclic complex with `Ext`-acyclic terms to an acyclic
complex. -/
theorem map_acyclic [HasExt.{max u v r t} (SheafOfModules.{max u v r t} R)] (a : ℤ)
    (Lc : CochainComplex (SheafOfModules.{max u v r t} R) ℤ) (hLc : Lc.IsStrictlyLE a)
    (hP : ∀ n, adj.extAcyclic (Lc.X n)) (hac : Lc.Acyclic) :
    ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj Lc).Acyclic := by
  let := Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, r, t} K O
  have := adj.rightAdjoint_preservesLimits.{0, 0}
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  have : F.Additive := adj.left_adjoint_additive
  have : PreservesFiniteColimits F :=
    (adj.leftAdjoint_preservesColimits.{0, 0}).preservesFiniteColimits
  have hF := adj.map_acyclic_of_extAcyclic Lc a hac hP
  have hFH : ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Lc)).Acyclic := by
    intro i
    rw [HomologicalComplex.exactAt_iff] at *
    exact (hF i).map H
  exact fun i => (hFH i).of_iso
    ((Functor.mapHomologicalComplexCompIso eF.symm (ComplexShape.up ℤ)).app Lc)

/-- Sheaves of modules have enough injectives and `Ext`, and `ℕ`-indexed colimits in them are
exact. -/
private theorem hasExt_and_hasExactColimitsOfShape_nat (J : GrothendieckTopology C)
    [HasSheafify J Ab.{max u v r t}] [J.WEqualsLocallyBijective Ab.{max u v r t}]
    (R : Sheaf J RingCat.{r}) :
    EnoughInjectives (SheafOfModules.{max u v r t} R) ∧
      HasExt.{max u v r t} (SheafOfModules.{max u v r t} R) ∧
      HasExactColimitsOfShape ℕ (SheafOfModules.{max u v r t} R) := by
  let := Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, r, t} J R
  have : AB5OfSize.{0, 0} (SheafOfModules.{max u v r t} R) := AB5OfSize_shrink _
  exact ⟨inferInstance, hasExt_of_enoughInjectives.{max u v r t} _, AB5OfSize.ofShape ℕ⟩

include adj e adjab eF in
/-- **Stacks 07AC, existence**, when lower shriek of abelian sheaves is exact: a functor `F'`
which is `F` followed by an exact functor — in particular `F` itself — has a left derived functor
defined on the whole unbounded derived category, by the criterion of Stacks 0794 run with the
class of objects that are `Ext`-acyclic for `F ⊣ G`. -/
theorem hasPointwiseLeftDerivedFunctor :
    (F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{max u v r t} R) (ComplexShape.up ℤ)) := by
  let := Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, r, t} K O
  obtain ⟨_, _, _⟩ := hasExt_and_hasExactColimitsOfShape_nat.{t, r, v, u} J R
  exact Functor.hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex F' adj.extAcyclic
    (fun _ _ => adj.extAcyclic_biprod) (exists_epi_extAcyclic.{t, r, v, u} adj Gab e adjab)
    (fun a Lc hLc hP hac => map_acyclic.{t, r, v, u} adj Gab e adjab F' H eF a Lc hLc hP hac)

include adj e adjab eF in
/-- **The left derived functor of `hasPointwiseLeftDerivedFunctor` is absolute**: whatever
left derived functor `LF` of `F'` is chosen, `LF ⋙ G'` is a left derived functor of `F' ⋙ G'`
for every functor `G'` out of `D(B)`, `LF` being computed by resolutions. -/
theorem isLeftDerivedFunctor_comp
    (LF : DerivedCategory (SheafOfModules.{max u v r t} R) ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶ F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{max u v r t} R) (ComplexShape.up ℤ))]
    {E : Type*} [Category E] (G' : DerivedCategory B ⥤ E) :
    (LF ⋙ G').IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh LF G').inv ≫ Functor.whiskerRight α G')
      (HomotopyCategory.quasiIso (SheafOfModules.{max u v r t} R) (ComplexShape.up ℤ)) := by
  let := Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, r, t} K O
  obtain ⟨_, _, _⟩ := hasExt_and_hasExactColimitsOfShape_nat.{t, r, v, u} J R
  exact Functor.isLeftDerivedFunctor_comp_of_acyclic_mapHomologicalComplex F' adj.extAcyclic
    (fun _ _ => adj.extAcyclic_biprod) (exists_epi_extAcyclic.{t, r, v, u} adj Gab e adjab)
    (fun a Lc hLc hP hac => map_acyclic.{t, r, v, u} adj Gab e adjab F' H eF a Lc hLc hP hac)
    DerivedCategory.Qh LF α G'

end LowerShriek

end Stacks.Cohomology.ExactAbelianLowerShriek

end
