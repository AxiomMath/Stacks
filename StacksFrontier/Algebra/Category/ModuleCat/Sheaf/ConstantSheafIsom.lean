module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafIsom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
import StacksCore.Tactic.StacksAttribute

/-!
# The constant sheaf on a set of isomorphisms

Let `(C, J)` be a site and `Λ` a commutative ring. For finitely presented `Λ`-modules `M` and `N`,
Stacks Tag 093T (2) asserts the isomorphism of sheaves of sets
`Isom_Λ(M, N)̲ = Isom_{Λ̲}(M̲, N̲)`,
where the left side is the constant sheaf on the set of `Λ`-linear isomorphisms `M ≃ₗ[Λ] N` and
the right side is the sheaf of isomorphisms of the two constant sheaves of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafIsom`. This file proves it, and deduces
part (4): for locally constant sheaves of `Λ`-modules `F` and `G` of finite presentation,
`Isom_{Λ̲}(F, G)` is a locally constant sheaf of sets.

## Main definitions

* `Stacks.ConstantSheaf.constantIsomNatTrans`: the comparison before sheafification, which sends a
  linear equivalence `e : M ≃ₗ[Λ] N` to the restriction to the slice site `C/X` of the isomorphism
  of constant sheaves `e̲`.
* `Stacks.ConstantSheaf.constantSheafIsomHom`: its factorization through the constant sheaf, i.e.
  the canonical map `Isom_Λ(M, N)̲ ⟶ Isom_{Λ̲}(M̲, N̲)`.
* `Stacks.ConstantSheaf.linearEquivOfInverse`: a morphism of `Λ`-modules with a two-sided inverse,
  read as a linear equivalence.
* `Stacks.ConstantSheaf.moduleSheafIsomMapIso`: `Isom_{Λ̲}(F, G)` transported along isomorphisms of
  its two arguments.
* `Stacks.ConstantSheaf.moduleSheafIsomOverPullbackIso`: `Isom_{Λ̲}(F, G)` commutes with
  restriction to a slice site.

## Main results

* `Stacks.ConstantSheaf.constantSheafIsomIso`: **Stacks Tag 093T (2)**.
* `Stacks.ConstantSheaf.isLocallyConstant_moduleSheafIsom`: **Stacks Tag 093T (4)**.
* `Stacks.ConstantSheaf.wEqualsLocallyBijective_type`: sheafification of presheaves of types
  inverts exactly the locally bijective morphisms, at any section universe containing the site.
* `Stacks.ConstantSheaf.isLocallySurjective_constantIsomNatTrans` and
  `Stacks.ConstantSheaf.isLocallyInjective_constantIsomNatTrans`: the two halves of the proof
  of part (2).

## Implementation notes

**The shape of the proof.** `Isom` has no universal property, so the comparison is not obtained
from an adjunction: it is the sheafification of the map which sends a linear equivalence to the
isomorphism of constant sheaves it induces, and the content is that this map is locally bijective.
Local bijectivity is turned into invertibility by
`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`
together with `Stacks.ConstantSheaf.wEqualsLocallyBijective_type`, which transports the sheafified
map's local bijectivity from the section universe `max u v` — where Mathlib has it — to the section
universe `max u v x` at which the statement lives.

**Both halves run through Tag 093T (1)**, in the form
`Stacks.ConstantSheaf.constantSheafHomIsoOfHom`, whose components are bijective. Local surjectivity
takes a section `α` of `Isom_{Λ̲}(M̲, N̲)` over `U`, reads `α` and its inverse through that
isomorphism as sections of `Hom_Λ(M, N)̲` and of `Hom_Λ(N, M)̲`, and refines `U` by a covering on
which both are constant, at `f : M ⟶ N` and at `k : N ⟶ M` say. Over such a member the two
composites `f ≫ k` and `k ≫ f` induce the same morphisms of constant sheaves as the identities, so
by the injectivity of the comparison the corresponding constant sections agree; local injectivity
of the sheafification map then forces the two composites to be the identities — except over an
object whose *empty* sieve is covering, where instead every sieve is covering and there is nothing
left to prove. Both branches are handled by
`Stacks.ConstantSheaf.eq_or_mem_of_equalizerSieve_const`. With `f` and `k` mutually inverse, `f`
is a linear equivalence whose image under the comparison is the restriction of `α`.

**Part (4) is local on `C`**, exactly as part (3) is in `LocallyConstantSheafHom.lean`: `F` and `G`
are trivialized simultaneously over a common refinement of their two trivializing coverings, and
over a member of it part (2) applies. The two structural ingredients that turn the local
computation into a statement about `Isom_{Λ̲}(F, G)` are proved here first — the functoriality
`Stacks.ConstantSheaf.moduleSheafIsomMapIso` and the compatibility with restriction
`Stacks.ConstantSheaf.moduleSheafIsomOverPullbackIso`. Both reduce to the corresponding statements
for the internal hom together with the observation that the comparison maps preserve *and reflect*
invertibility of a section: conjugation by isomorphisms does, and restriction along the
iterated-slice functor does because the equivalence of sheaf categories inverting it both preserves
and reflects isomorphisms.

The hypothesis carried on `F` and `G` is
`Stacks.ConstantSheaf.IsFinitePresentationLocallyConstantModuleSheaf`, local constancy with
finitely presented constant values, for the reason recorded in the implementation notes of
`LocallyConstantSheafHom.lean`: for a locally constant sheaf it agrees with the source's finite
presentation of the sheaf by Tag 093N (2), and it is the form the proof consumes.

**Universes.** As in the companion files the module universe is `max u v x`: the internal hom of
two sheaves of `ModuleCat.{x} Λ`-valued sheaves raises the module universe to `max u v x`, so this
is the only universe at which `Isom_{Λ̲}(M̲, N̲)` is an object of the same category of sheaves of
sets as `Isom_Λ(M, N)̲`. The sheaf of sets accordingly has sections in `Type (max u v x)`, which is
why the local bijectivity criterion is needed outside Mathlib's `Type (max u v)`.

**`Λ` is a commutative ring**, where Stacks says only "a ring". Since the source states the two
sides as sheaves of `Λ`-modules and of sets of `Λ`-linear isomorphisms, this is a benign
strengthening, and it is the one the ambient files already carry.

## References

* [Stacks Project, Tag 093T](https://stacks.math.columbia.edu/tag/093T)
* [Stacks Project, Tag 093N](https://stacks.math.columbia.edu/tag/093N)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w x t

namespace Stacks.ConstantSheaf

/-! ### Linear equivalences and isomorphisms of modules -/

section LinearEquiv

variable (Λ : Type w) [CommRing Λ]

/-- The morphism of `Λ`-modules underlying a linear equivalence is an isomorphism. -/
instance isIso_ofHom_toLinearMap {M N : ModuleCat.{t} Λ} (e : M ≃ₗ[Λ] N) :
    IsIso (ModuleCat.ofHom e.toLinearMap) :=
  ⟨ModuleCat.ofHom e.symm.toLinearMap, by ext m; simp, by ext m; simp⟩

/-- A morphism of `Λ`-modules with a two-sided inverse, read as a linear equivalence. -/
noncomputable def linearEquivOfInverse {M N : ModuleCat.{t} Λ} (f : M ⟶ N) (g : N ⟶ M)
    (h₁ : f ≫ g = 𝟙 M) (h₂ : g ≫ f = 𝟙 N) : M ≃ₗ[Λ] N :=
  LinearEquiv.ofLinearMap f.hom g.hom
    (by ext n; exact ConcreteCategory.congr_hom h₂ n)
    (by ext m; exact ConcreteCategory.congr_hom h₁ m)

/-- The linear equivalence built from a two-sided inverse has the given morphism underneath. -/
theorem ofHom_linearEquivOfInverse {M N : ModuleCat.{t} Λ} (f : M ⟶ N) (g : N ⟶ M)
    (h₁ : f ≫ g = 𝟙 M) (h₂ : g ≫ f = 𝟙 N) :
    ModuleCat.ofHom (linearEquivOfInverse Λ f g h₁ h₂).toLinearMap = f :=
  rfl

/-- A linear equivalence is determined by its underlying morphism of modules. -/
theorem linearEquiv_eq_of_ofHom_eq {M N : ModuleCat.{t} Λ} {e₁ e₂ : M ≃ₗ[Λ] N}
    (h : ModuleCat.ofHom e₁.toLinearMap = ModuleCat.ofHom e₂.toLinearMap) : e₁ = e₂ :=
  LinearEquiv.toLinearMap_injective (ModuleCat.hom_ext_iff.mp h)

end LinearEquiv

/-! ### Sheafification of presheaves of types in a universe containing the site -/

section TypeSheafification

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [UnivLE.{max u v, t}] [HasWeakSheafify J (Type t)]

/-- Sheafification of a presheaf of types is locally injective, at any section universe
containing the site. Mathlib's instance is pinned to the section universe `max u v`. -/
theorem isLocallyInjective_toSheafify_type (P : Cᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) :=
  have := GrothendieckTopology.isLocallyInjective_toSheafify_type_of_univLE J P
  (Presheaf.isLocallyInjective_iff_of_fac J
    (toSheafify_plusPlusIsoSheafify_hom J (Type t) P)).2 inferInstance

/-- Sheafification of a presheaf of types is locally surjective, at any section universe
containing the site. -/
theorem isLocallySurjective_toSheafify_type (P : Cᵒᵖ ⥤ Type t) :
    Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) :=
  have := GrothendieckTopology.isLocallySurjective_toSheafify_type_of_univLE J P
  (Presheaf.isLocallySurjective_iff_of_fac J
    (toSheafify_plusPlusIsoSheafify_hom J (Type t) P)).2 inferInstance

/-- **`J.W` is local bijectivity for presheaves of types** at any section universe containing the
site. Mathlib provides this only at the section universe `max u v`; it holds in any universe
containing it, which is the universe in which the sections of `Isom_{Λ̲}(M̲, N̲)` live. -/
instance wEqualsLocallyBijective_type : J.WEqualsLocallyBijective (Type t) :=
  have := isLocallyInjective_toSheafify_type.{u, v, t} J
  have := isLocallySurjective_toSheafify_type.{u, v, t} J
  GrothendieckTopology.WEqualsLocallyBijective.mk' J (Type t)

end TypeSheafification

section OverTypeSheafification

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Sheafification of presheaves of sets on a slice site, in a universe containing the ambient
site. This is already available, but only through an instance whose section universe is `max u v`
for the slice site's own universes, which the unifier cannot match against `max u v x` for the
ambient site's; stating it at that shape is what makes local constancy of a sheaf of sets with
sections in `Type (max u v x)` a well-formed assertion. -/
instance hasWeakSheafify_over_type (U : C) :
    HasWeakSheafify (J.over U) (Type (max u v x)) :=
  inferInstance

end OverTypeSheafification

/-! ### Sections of a constant presheaf of modules which agree locally -/

section ConstantPresheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type w) [CommRing Λ]

/-- Two sections of a *constant* presheaf of `Λ`-modules whose equalizer sieve is covering are
equal — unless the empty sieve is covering over the object in question, in which case every sieve
over it is covering and the conclusion of any local statement there is free. The restriction maps
of a constant presheaf are the identity, so its equalizer sieves are only `⊤` and `⊥`. -/
theorem eq_or_mem_of_equalizerSieve_const (E : ModuleCat.{max u v x} Λ) {X : Cᵒᵖ}
    (a b : (E : Type (max u v x)))
    (h : Presheaf.equalizerSieve (F := (Functor.const Cᵒᵖ).obj E) a b ∈ J X.unop)
    (S : Sieve X.unop) : a = b ∨ S ∈ J X.unop := by
  by_cases hab : a = b
  · exact Or.inl hab
  · refine Or.inr (J.superset_covering (le_trans ?_ bot_le) h)
    intro Y f hf
    exact hab (by simpa using hf)

end ConstantPresheaf

/-! ### The comparison of Tag 093T (2) -/

section Isom

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type w) [CommRing Λ]
variable (M N : ModuleCat.{max u v x} Λ)

/-- The restriction to a slice site of the morphism of constant sheaves induced by an isomorphism
of `Λ`-modules is an isomorphism. -/
theorem isIso_overPullback_map_constantSheaf_map (X : Cᵒᵖ) (f : M ⟶ N) [IsIso f] :
    IsIso ((J.overPullback (ModuleCat.{max u v x} Λ) X.unop).map
      ((constantSheaf J (ModuleCat.{max u v x} Λ)).map f)) :=
  inferInstance

/-- The section of `Isom_{Λ̲}(M̲, N̲)` over `X` determined by a linear equivalence `M ≃ₗ[Λ] N`:
the restriction to the slice site `C/X` of the isomorphism of constant sheaves it induces. -/
noncomputable def constantIsomSection (X : Cᵒᵖ)
    (e : (M : Type (max u v x)) ≃ₗ[Λ] (N : Type (max u v x))) :
    (moduleSheafIsom J Λ ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj M)
      ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj N)).obj.obj X :=
  ⟨(J.overPullback (ModuleCat.{max u v x} Λ) X.unop).map
      ((constantSheaf J (ModuleCat.{max u v x} Λ)).map (ModuleCat.ofHom e.toLinearMap)),
    isIso_overPullback_map_constantSheaf_map J Λ M N X (ModuleCat.ofHom e.toLinearMap)⟩

/-- **The comparison of Tag 093T (2), before sheafification.** A linear equivalence
`e : M ≃ₗ[Λ] N` is sent to the constant section of `Isom_{Λ̲}(M̲, N̲)` given by the isomorphism of
constant sheaves `e̲`. -/
noncomputable def constantIsomNatTrans :
    (Functor.const Cᵒᵖ).obj ((M : Type (max u v x)) ≃ₗ[Λ] (N : Type (max u v x))) ⟶
      (moduleSheafIsom J Λ ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj M)
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj N)).obj where
  app X := ↾fun e => constantIsomSection J Λ M N X e
  naturality _ _ _ := ConcreteCategory.hom_ext _ _ fun _ => Subtype.ext rfl

/-- The comparison sends a linear equivalence to the restriction of the morphism of constant
sheaves induced by its underlying morphism of modules. -/
theorem constantIsomNatTrans_app_apply (X : Cᵒᵖ)
    (e : (M : Type (max u v x)) ≃ₗ[Λ] (N : Type (max u v x))) :
    ((constantIsomNatTrans J Λ M N).app X e).1 =
      (J.overPullback (ModuleCat.{max u v x} Λ) X.unop).map
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).map (ModuleCat.ofHom e.toLinearMap)) :=
  rfl

/-- Each component of the isomorphism of Tag 093T (1) is bijective. -/
theorem bijective_constantSheafHomIsoOfHom_app
    [Module.FinitePresentation Λ (M : Type (max u v x))] (X : Cᵒᵖ) :
    Function.Bijective ((constantSheafHomIsoOfHom J Λ M N).hom.hom.app X).hom := by
  have h : IsIso ((constantSheafHomIsoOfHom J Λ M N).hom.hom) :=
    Functor.map_isIso (sheafToPresheaf J (ModuleCat.{max u v x} Λ))
      (constantSheafHomIsoOfHom J Λ M N).hom
  rw [← ConcreteCategory.isIso_iff_bijective]
  infer_instance

/-- **Tag 093T (1) is the canonical comparison**, in the form in which `Hom_Λ(M, N)` is the
morphism type of the category of `Λ`-modules: the constant section determined by `f : M ⟶ N` is
sent to the restriction of `f̲`. -/
theorem constantSheafHomIsoOfHom_hom_app_apply
    [Module.FinitePresentation Λ (M : Type (max u v x))] (X : Cᵒᵖ) (f : M ⟶ N) :
    ((constantSheafHomIsoOfHom J Λ M N).hom.hom.app X).hom
        (((constantUnit J Λ (ModuleCat.of Λ (M ⟶ N))).app X).hom f) =
      (J.overPullback (ModuleCat.{max u v x} Λ) X.unop).map
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).map f) := by
  have h := constantSheafHomIso_hom_app_apply J Λ M N (ModuleCat.of Λ (M ⟶ N))
    (ModuleCat.homLinearEquiv (S := Λ)).symm X f
  rwa [LinearEquiv.symm_apply_apply] at h

/-- Over a member of a covering on which the section of `Hom_Λ(M, N)̲` corresponding to a section
of the internal hom becomes the constant section at `f : M ⟶ N`, the restriction of that section
is the restriction of `f̲`. -/
theorem overMapPullback_map_constantSheafHomIsoOfHom_app
    [Module.FinitePresentation Λ (M : Type (max u v x))] {U V : C} (g : V ⟶ U)
    (a : (((constantSheaf J (ModuleCat.{max u v x} Λ)).obj
      (ModuleCat.of Λ (M ⟶ N))).obj.obj (op U) : Type (max u v x)))
    (f : M ⟶ N)
    (hf : ((constantUnit J Λ (ModuleCat.of Λ (M ⟶ N))).app (op V)).hom f =
      ((((constantSheaf J (ModuleCat.{max u v x} Λ)).obj
        (ModuleCat.of Λ (M ⟶ N))).obj.map g.op)).hom a) :
    (J.overMapPullback (ModuleCat.{max u v x} Λ) g).map
        (((constantSheafHomIsoOfHom J Λ M N).hom.hom.app (op U)).hom a) =
      (J.overPullback (ModuleCat.{max u v x} Λ) V).map
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).map f) := by
  have hnat := ConcreteCategory.congr_hom
    ((constantSheafHomIsoOfHom J Λ M N).hom.hom.naturality g.op) a
  simp only [ConcreteCategory.comp_apply] at hnat
  rw [← hf, constantSheafHomIsoOfHom_hom_app_apply] at hnat
  exact hnat.symm

/-- Two morphisms of `Λ`-modules which induce the same morphism of constant sheaves after
restriction to a slice site agree, unless the empty sieve is covering there — in which case every
sieve is covering. -/
theorem eq_or_mem_of_overPullback_map_eq
    [Module.FinitePresentation Λ (M : Type (max u v x))] {V : C} (f₁ f₂ : M ⟶ N)
    (h : (J.overPullback (ModuleCat.{max u v x} Λ) V).map
          ((constantSheaf J (ModuleCat.{max u v x} Λ)).map f₁) =
        (J.overPullback (ModuleCat.{max u v x} Λ) V).map
          ((constantSheaf J (ModuleCat.{max u v x} Λ)).map f₂))
    (S : Sieve V) : f₁ = f₂ ∨ S ∈ J V := by
  have hli : Presheaf.IsLocallyInjective J
      (constantUnit J Λ (ModuleCat.of Λ (M ⟶ N))) :=
    isLocallyInjective_toSheafify_moduleCat.{v, u, x, w} J Λ _
  have key : ((constantUnit J Λ (ModuleCat.of Λ (M ⟶ N))).app (op V)).hom f₁ =
      ((constantUnit J Λ (ModuleCat.of Λ (M ⟶ N))).app (op V)).hom f₂ :=
    (bijective_constantSheafHomIsoOfHom_app J Λ M N (op V)).injective
      (((constantSheafHomIsoOfHom_hom_app_apply J Λ M N (op V) f₁).trans h).trans
        (constantSheafHomIsoOfHom_hom_app_apply J Λ M N (op V) f₂).symm)
  exact eq_or_mem_of_equalizerSieve_const J Λ (ModuleCat.of Λ (M ⟶ N)) f₁ f₂
    (Presheaf.equalizerSieve_mem J (constantUnit J Λ (ModuleCat.of Λ (M ⟶ N))) f₁ f₂ key) S

/-- **Local injectivity of the comparison of Tag 093T (2).** Two linear equivalences inducing the
same section of `Isom_{Λ̲}(M̲, N̲)` agree, because the comparison of Tag 093T (1) is injective on
sections and the sheafification map of a constant presheaf is locally injective. -/
theorem isLocallyInjective_constantIsomNatTrans
    [Module.FinitePresentation Λ (M : Type (max u v x))] :
    Presheaf.IsLocallyInjective J (constantIsomNatTrans J Λ M N) where
  equalizerSieve_mem {X} e₁ e₂ h := by
    have hval := congrArg Subtype.val h
    rw [constantIsomNatTrans_app_apply, constantIsomNatTrans_app_apply] at hval
    rcases eq_or_mem_of_overPullback_map_eq J Λ M N (ModuleCat.ofHom e₁.toLinearMap)
      (ModuleCat.ofHom e₂.toLinearMap) hval (Presheaf.equalizerSieve e₁ e₂) with he | hS
    · rw [linearEquiv_eq_of_ofHom_eq Λ he, Presheaf.equalizerSieve_self_eq_top]
      exact J.top_mem _
    · exact hS

/-- **Local surjectivity of the comparison of Tag 093T (2).** A section of `Isom_{Λ̲}(M̲, N̲)` is,
on a covering, the section determined by a linear equivalence: both it and its inverse become
constant morphisms of modules on a covering by Tag 093T (1), and over a member of that covering the
two composites are the identity because the comparison of Tag 093T (1) is injective on sections and
the sheafification map of a constant presheaf is locally injective. -/
theorem isLocallySurjective_constantIsomNatTrans
    [Module.FinitePresentation Λ (M : Type (max u v x))]
    [Module.FinitePresentation Λ (N : Type (max u v x))] :
    Presheaf.IsLocallySurjective J (constantIsomNatTrans J Λ M N) where
  imageSieve_mem {U} s := by
    classical
    have hsM : Presheaf.IsLocallySurjective J
        (constantUnit J Λ (ModuleCat.of Λ (M ⟶ N))) :=
      isLocallySurjective_toSheafify_moduleCat.{v, u, x, w} J Λ _
    have hsN : Presheaf.IsLocallySurjective J
        (constantUnit J Λ (ModuleCat.of Λ (N ⟶ M))) :=
      isLocallySurjective_toSheafify_moduleCat.{v, u, x, w} J Λ _
    obtain ⟨α, hα⟩ := s
    have hα' : IsIso α := hα
    obtain ⟨a, ha⟩ := (bijective_constantSheafHomIsoOfHom_app J Λ M N (op U)).surjective α
    obtain ⟨b, hb⟩ := (bijective_constantSheafHomIsoOfHom_app J Λ N M (op U)).surjective (inv α)
    refine J.transitive (J.intersection_covering
      (Presheaf.imageSieve_mem J (constantUnit J Λ (ModuleCat.of Λ (M ⟶ N))) a)
      (Presheaf.imageSieve_mem J (constantUnit J Λ (ModuleCat.of Λ (N ⟶ M))) b)) _ ?_
    intro V g hg
    obtain ⟨f, hf⟩ := hg.1
    obtain ⟨k, hk⟩ := hg.2
    -- the restrictions of `α` and of its inverse are the restrictions of `f̲` and of `k̲`
    have hfV : (J.overMapPullback (ModuleCat.{max u v x} Λ) g).map α =
        (J.overPullback (ModuleCat.{max u v x} Λ) V).map
          ((constantSheaf J (ModuleCat.{max u v x} Λ)).map f) := by
      rw [← ha]
      exact overMapPullback_map_constantSheafHomIsoOfHom_app J Λ M N g a f hf
    have hkV : (J.overMapPullback (ModuleCat.{max u v x} Λ) g).map (inv α) =
        (J.overPullback (ModuleCat.{max u v x} Λ) V).map
          ((constantSheaf J (ModuleCat.{max u v x} Λ)).map k) := by
      rw [← hb]
      exact overMapPullback_map_constantSheafHomIsoOfHom_app J Λ N M g b k hk
    -- hence the two composites induce the identity after restriction
    have hid₁ := comp_overMapPullback_map_eq_id J g α (inv α) (IsIso.hom_inv_id α)
    have hid₂ := overMapPullback_map_comp_eq_id J g α (inv α) (IsIso.inv_hom_id α)
    have comp_id : ∀ (P Q : ModuleCat.{max u v x} Λ) [Module.FinitePresentation Λ P]
        (f : P ⟶ Q) (k : Q ⟶ P),
        (J.overPullback (ModuleCat.{max u v x} Λ) V).map
            ((constantSheaf J (ModuleCat.{max u v x} Λ)).map f) ≫
          (J.overPullback (ModuleCat.{max u v x} Λ) V).map
            ((constantSheaf J (ModuleCat.{max u v x} Λ)).map k) = 𝟙 _ →
        f ≫ k = 𝟙 P ∨
          (Presheaf.imageSieve (constantIsomNatTrans J Λ M N) ⟨α, hα⟩).pullback g ∈ J V :=
      fun P Q _ f k h => eq_or_mem_of_overPullback_map_eq J Λ P P (f ≫ k) (𝟙 P)
        (by
          rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
            CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
          exact h) _
    rcases comp_id M N f k (by rw [← hfV, ← hkV]; exact hid₁) with h₁ | hS
    swap
    · exact hS
    rcases comp_id N M k f (by rw [← hfV, ← hkV]; exact hid₂) with h₂ | hS
    swap
    · exact hS
    -- `f` is a linear equivalence whose comparison is the restriction of `α`
    have hmem : Presheaf.imageSieve (constantIsomNatTrans J Λ M N)
        (⟨α, hα⟩ : (moduleSheafIsom J Λ ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj M)
          ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj N)).obj.obj (op U)) g :=
      ⟨linearEquivOfInverse Λ f k h₁ h₂, Subtype.ext (by
        rw [constantIsomNatTrans_app_apply, ofHom_linearEquivOfInverse]
        exact hfV.symm)⟩
    rw [Sieve.pullback_eq_top_of_mem _ hmem]
    exact J.top_mem V

/-- **The canonical map of Stacks Tag 093T (2)**,
`Isom_Λ(M, N)̲ ⟶ Isom_{Λ̲}(M̲, N̲)`:
the map which sends a linear equivalence to the isomorphism of constant sheaves it induces,
factored through the constant sheaf by the universal property of sheafification. That it is an
isomorphism, which is the content of part (2), is
`Stacks.ConstantSheaf.constantSheafIsomIso`. -/
@[stacks 093T "constant Isom"]
noncomputable def constantSheafIsomHom :
    (constantSheaf J (Type (max u v x))).obj
        ((M : Type (max u v x)) ≃ₗ[Λ] (N : Type (max u v x))) ⟶
      moduleSheafIsom J Λ ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj M)
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj N) :=
  ⟨sheafifyLift J (constantIsomNatTrans J Λ M N)
    (moduleSheafIsom J Λ ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj M)
      ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj N)).property⟩

/-- The comparison map factors the pre-sheafification comparison through the constant sheaf. -/
theorem toSheafify_constantSheafIsomHom :
    CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj
          ((M : Type (max u v x)) ≃ₗ[Λ] (N : Type (max u v x)))) ≫
        (constantSheafIsomHom J Λ M N).hom =
      constantIsomNatTrans J Λ M N :=
  toSheafify_sheafifyLift J _ _

/-- The comparison map is locally injective, because it is so before sheafification and the
sheafification map of a presheaf of types is locally bijective. -/
theorem isLocallyInjective_constantSheafIsomHom
    [Module.FinitePresentation Λ (M : Type (max u v x))] :
    Presheaf.IsLocallyInjective J (constantSheafIsomHom J Λ M N).hom := by
  have h := isLocallyInjective_constantIsomNatTrans J Λ M N
  rw [← toSheafify_constantSheafIsomHom] at h
  exact (Presheaf.comp_isLocallyInjective_iff J (CategoryTheory.toSheafify J
    ((Functor.const Cᵒᵖ).obj ((M : Type (max u v x)) ≃ₗ[Λ] (N : Type (max u v x))))) _).1 h

/-- The comparison map is locally surjective, for the same reason. -/
theorem isLocallySurjective_constantSheafIsomHom
    [Module.FinitePresentation Λ (M : Type (max u v x))]
    [Module.FinitePresentation Λ (N : Type (max u v x))] :
    Presheaf.IsLocallySurjective J (constantSheafIsomHom J Λ M N).hom := by
  have := isLocallySurjective_constantIsomNatTrans J Λ M N
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
    (toSheafify_constantSheafIsomHom J Λ M N)

/-- For finitely presented `M` and `N`, the comparison map
`Stacks.ConstantSheaf.constantSheafIsomHom` is an isomorphism of sheaves. -/
instance isIso_constantSheafIsomHom
    [Module.FinitePresentation Λ (M : Type (max u v x))]
    [Module.FinitePresentation Λ (N : Type (max u v x))] :
    IsIso (constantSheafIsomHom J Λ M N) :=
  (Sheaf.isLocallyBijective_iff_isIso (constantSheafIsomHom J Λ M N)).1
    ⟨isLocallyInjective_constantSheafIsomHom J Λ M N,
      isLocallySurjective_constantSheafIsomHom J Λ M N⟩

/-- **Stacks Project, Tag 093T (2).** `Isom_Λ(M, N)̲ ≅ Isom_{Λ̲}(M̲, N̲)` for finitely presented
`M` and `N`, as sheaves of sets. The comparison is the canonical one: it sends the constant section
given by a linear equivalence `e` to the restriction of the isomorphism of constant sheaves `e̲`,
which is `Stacks.ConstantSheaf.toSheafify_constantSheafIsomHom` together with
`Stacks.ConstantSheaf.constantIsomNatTrans_app_apply`. -/
@[stacks 093T "constant Isom"]
noncomputable def constantSheafIsomIso
    [Module.FinitePresentation Λ (M : Type (max u v x))]
    [Module.FinitePresentation Λ (N : Type (max u v x))] :
    (constantSheaf J (Type (max u v x))).obj
        ((M : Type (max u v x)) ≃ₗ[Λ] (N : Type (max u v x))) ≅
      moduleSheafIsom J Λ ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj M)
        ((constantSheaf J (ModuleCat.{max u v x} Λ)).obj N) :=
  asIso (constantSheafIsomHom J Λ M N)

end Isom

/-! ### `Isom` transported along isomorphisms of its arguments -/

section Functoriality

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type w) [CommRing Λ]

/-- Conjugating an invertible local morphism by the restrictions of two isomorphisms gives an
invertible local morphism. -/
theorem isIso_moduleSheafHomMap_app {F F' G G' : Sheaf J (ModuleCat.{max u v x} Λ)}
    (u : F' ⟶ F) (w : G ⟶ G') [IsIso u] [IsIso w] (X : Cᵒᵖ)
    (α : (moduleSheafHom J Λ F G).obj.obj X) (hα : IsIso α) :
    IsIso ((moduleSheafHomMap J Λ u w).hom.app X α) := by
  rw [moduleSheafHomMap_app_apply]
  exact IsIso.comp_isIso'
    (Functor.map_isIso (J.overPullback (ModuleCat.{max u v x} Λ) X.unop) u)
    (IsIso.comp_isIso' hα
      (Functor.map_isIso (J.overPullback (ModuleCat.{max u v x} Λ) X.unop) w))

/-- The map `Isom_{Λ̲}(F, G) ⟶ Isom_{Λ̲}(F', G')` attached to isomorphisms `u : F' ⟶ F` and
`w : G ⟶ G'`: an invertible local morphism is conjugated by their restrictions, which leaves it
invertible. -/
def moduleSheafIsomMap {F F' G G' : Sheaf J (ModuleCat.{max u v x} Λ)}
    (u : F' ⟶ F) (w : G ⟶ G') [IsIso u] [IsIso w] :
    moduleSheafIsom J Λ F G ⟶ moduleSheafIsom J Λ F' G' :=
  ⟨{ app X := ↾fun s =>
       ⟨(moduleSheafHomMap J Λ u w).hom.app X s.1,
         isIso_moduleSheafHomMap_app J Λ u w X s.1 s.2⟩
     naturality _ _ _ := ConcreteCategory.hom_ext _ _ fun _ => Subtype.ext rfl }⟩

/-- **`Isom_{Λ̲}(F, G)` transported along isomorphisms of its two arguments.** -/
noncomputable def moduleSheafIsomMapIso {F F' G G' : Sheaf J (ModuleCat.{max u v x} Λ)}
    (eF : F ≅ F') (eG : G ≅ G') :
    moduleSheafIsom J Λ F G ≅ moduleSheafIsom J Λ F' G' where
  hom := moduleSheafIsomMap J Λ eF.inv eG.hom
  inv := moduleSheafIsomMap J Λ eF.hom eG.inv
  hom_inv_id := Sheaf.hom_ext <| NatTrans.ext <| funext fun X =>
    ConcreteCategory.hom_ext _ _ fun s =>
      Subtype.ext (map_hom_comp_map_inv_conj J Λ eF eG X.unop s.1)
  inv_hom_id := Sheaf.hom_ext <| NatTrans.ext <| funext fun X =>
    ConcreteCategory.hom_ext _ _ fun s =>
      Subtype.ext (map_hom_comp_map_inv_conj J Λ eF.symm eG.symm X.unop s.1)

end Functoriality

/-! ### `Isom` commutes with restriction to a slice site -/

section Slice

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type w) [CommRing Λ]
variable (X : C) (F G : Sheaf J (ModuleCat.{max u v x} Λ))

/-- A local morphism on `C/R.left` is invertible exactly when it is invertible read as a morphism
on the iterated slice `(C/X)/R`: the two are exchanged by an equivalence of sheaf categories, which
both preserves and reflects invertibility. -/
theorem isIso_moduleSheafHomSliceSection_iff (R : Over X)
    (α : (J.overPullback (ModuleCat.{max u v x} Λ) R.left).obj F ⟶
      (J.overPullback (ModuleCat.{max u v x} Λ) R.left).obj G) :
    IsIso (moduleSheafHomSliceSection J Λ X F G R α) ↔ IsIso α := by
  constructor
  · intro h
    rw [← moduleSheafSliceCongr_functor_map_sliceSection J Λ X F G R α]
    exact Functor.map_isIso (moduleSheafSliceCongr J Λ X R).functor _
  · intro h
    have h' : IsIso ((moduleSheafSliceCongr J Λ X R).functor.map
        (moduleSheafHomSliceSection J Λ X F G R α)) := by
      rw [moduleSheafSliceCongr_functor_map_sliceSection]
      exact h
    exact isIso_of_reflects_iso _ (moduleSheafSliceCongr J Λ X R).functor

/-- Reading an invertible section of the internal hom on the slice site, as a morphism of
presheaves of sets on `C/X`. -/
noncomputable def moduleSheafIsomOverPullbackNatTrans :
    ((J.overPullback (Type (max u v x)) X).obj (moduleSheafIsom J Λ F G)).obj ⟶
      (moduleSheafIsom (J.over X) Λ ((J.overPullback (ModuleCat.{max u v x} Λ) X).obj F)
        ((J.overPullback (ModuleCat.{max u v x} Λ) X).obj G)).obj where
  app R := ↾fun s => ⟨moduleSheafHomSliceSection J Λ X F G R.unop s.1,
    (isIso_moduleSheafHomSliceSection_iff J Λ X F G R.unop s.1).2 s.2⟩
  naturality _ _ _ := ConcreteCategory.hom_ext _ _ fun _ => Subtype.ext rfl

/-- Each component of `Stacks.ConstantSheaf.moduleSheafIsomOverPullbackNatTrans` is bijective: the
underlying map on sections of the internal hom is, and invertibility is exchanged in both
directions. -/
theorem bijective_moduleSheafIsomOverPullbackNatTrans_app (R : (Over X)ᵒᵖ) :
    Function.Bijective (ConcreteCategory.hom
      ((moduleSheafIsomOverPullbackNatTrans J Λ X F G).app R)) := by
  have hb := bijective_moduleSheafHomOverPullbackNatTrans_app J Λ X F G R
  refine ⟨fun s t hst => Subtype.ext (hb.injective (congrArg Subtype.val hst)), ?_⟩
  intro β
  obtain ⟨α, hα⟩ := hb.surjective β.1
  refine ⟨⟨α, (isIso_moduleSheafHomSliceSection_iff J Λ X F G R.unop α).1 ?_⟩,
    Subtype.ext hα⟩
  rw [show moduleSheafHomSliceSection J Λ X F G R.unop α = β.1 from hα]
  exact β.2

/-- Each component of `Stacks.ConstantSheaf.moduleSheafIsomOverPullbackNatTrans` is an
isomorphism. -/
instance isIso_moduleSheafIsomOverPullbackNatTrans_app (R : (Over X)ᵒᵖ) :
    IsIso ((moduleSheafIsomOverPullbackNatTrans J Λ X F G).app R) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_moduleSheafIsomOverPullbackNatTrans_app J Λ X F G R

/-- The inverse of `Stacks.ConstantSheaf.moduleSheafIsomOverPullbackNatTrans`, assembled from the
inverses of its components. -/
noncomputable def moduleSheafIsomOverPullbackNatTransInv :
    (moduleSheafIsom (J.over X) Λ ((J.overPullback (ModuleCat.{max u v x} Λ) X).obj F)
        ((J.overPullback (ModuleCat.{max u v x} Λ) X).obj G)).obj ⟶
      ((J.overPullback (Type (max u v x)) X).obj (moduleSheafIsom J Λ F G)).obj where
  app R := inv ((moduleSheafIsomOverPullbackNatTrans J Λ X F G).app R)
  naturality _ _ f := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact ((moduleSheafIsomOverPullbackNatTrans J Λ X F G).naturality f).symm

/-- **`Isom` commutes with restriction to a slice site.** The restriction to `C/X` of
`Isom_{Λ̲}(F, G)` is the sheaf of isomorphisms of the restrictions of `F` and `G` to `C/X`. -/
noncomputable def moduleSheafIsomOverPullbackIso :
    (J.overPullback (Type (max u v x)) X).obj (moduleSheafIsom J Λ F G) ≅
      moduleSheafIsom (J.over X) Λ ((J.overPullback (ModuleCat.{max u v x} Λ) X).obj F)
        ((J.overPullback (ModuleCat.{max u v x} Λ) X).obj G) :=
  { hom := ⟨moduleSheafIsomOverPullbackNatTrans J Λ X F G⟩
    inv := ⟨moduleSheafIsomOverPullbackNatTransInv J Λ X F G⟩
    hom_inv_id := Sheaf.hom_ext <| NatTrans.ext <| funext fun _ => IsIso.hom_inv_id _
    inv_hom_id := Sheaf.hom_ext <| NatTrans.ext <| funext fun _ => IsIso.inv_hom_id _ }

end Slice

/-! ### Tag 093T (4) -/

section Main

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type w) [CommRing Λ]

/-- If `F` and `G` are locally constant sheaves of `Λ`-modules of finite presentation, then
`Isom_{Λ̲}(F, G)` is a locally constant sheaf of sets. The assertion is local on `C`, so `F` and `G`
may be trivialized simultaneously; over a member of the resulting covering they are the constant
sheaves on finitely presented modules `M` and `N`, and then
`Stacks.ConstantSheaf.constantSheafIsomIso` identifies `Isom_{Λ̲}(F, G)` with the constant sheaf on
`M ≃ₗ[Λ] N`. -/
@[stacks 093T "Isom of locally constant sheaves"]
theorem isLocallyConstant_moduleSheafIsom (F G : Sheaf J (ModuleCat.{max u v x} Λ))
    (hF : IsFinitePresentationLocallyConstantModuleSheaf J Λ F)
    (hG : IsFinitePresentationLocallyConstantModuleSheaf J Λ G) :
    IsLocallyConstant J (moduleSheafIsom J Λ F G) where
  exists_cover U := by
    obtain ⟨I, V, f, hf, hFV⟩ := hF U
    obtain ⟨I', W, g, hg, hGW⟩ := hG U
    obtain ⟨K, Z, p, hp⟩ := (Sieve.ofArrows V f ⊓ Sieve.ofArrows W g).exists_eq_ofArrows
    refine ⟨K, Z, p, hp ▸ J.intersection_covering hf hg, fun k => ?_⟩
    have hk : (Sieve.ofArrows V f ⊓ Sieve.ofArrows W g) (p k) := by
      rw [hp]
      exact Sieve.ofArrows_mk Z p k
    obtain ⟨i, a, -⟩ := (Sieve.mem_ofArrows_iff V f (p k)).mp hk.1
    obtain ⟨j, b, -⟩ := (Sieve.mem_ofArrows_iff W g (p k)).mp hk.2
    obtain ⟨M, hM, ⟨eF⟩⟩ := hFV i
    obtain ⟨N, hN, ⟨eG⟩⟩ := hGW j
    have := hM
    have := hN
    exact ⟨⟨(M : Type (max u v x)) ≃ₗ[Λ] (N : Type (max u v x)),
      ⟨constantSheafIsomIso (J.over (Z k)) Λ M N ≪≫
        moduleSheafIsomMapIso (J.over (Z k)) Λ
          (overPullbackIsoOfMapModule J a F M eF)
          (overPullbackIsoOfMapModule J b G N eG) ≪≫
        (moduleSheafIsomOverPullbackIso J Λ (Z k) F G).symm⟩⟩⟩

end Main

end Stacks.ConstantSheaf

end
