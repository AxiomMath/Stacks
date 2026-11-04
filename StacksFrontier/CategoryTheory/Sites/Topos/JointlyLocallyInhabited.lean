module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# Joint local inhabitedness of a family of sheaves of types, and its inverse image

A family `A : ι → Sheaf K (Type w)` of sheaves of types on a site is *jointly locally
inhabited* when every object of the site is covered by objects over which some member of the
family has a section.  Equivalently, the images of the maps `A i ⟶ ⊤` cover the terminal
sheaf.  This file proves that the inverse image of a jointly locally inhabited family along a
morphism of topoi is again jointly locally inhabited
(`Stacks.Topos.jointlyLocallyInhabited_inverseImage`), and records the consequence in the form
of a covering of each object of the source site
(`Stacks.Topos.exists_cover_inverseImage_sections`).

For a family with a single member this is the statement that `f⁻¹` preserves local
surjectivity of `G ⟶ ⊤`, which is a special case of the fact that a left adjoint preserves
strong epimorphisms.  For a general family that route is not available: the joint statement is
local surjectivity of `∐ i, A i ⟶ ⊤`, and `Sheaf K (Type w)` is not known to have coproducts
— sheafification of type-valued presheaves is available in Mathlib only at the universe
`max u v` of the site, whereas `w` is unrelated to it here.

The proof given instead needs no colimits at all.  Write `S ⊆ ⊤` for the subsheaf of the
terminal sheaf of the *source* site whose sections over `U` record that `U` is covered by
objects carrying a section of some `f⁻¹(A i)`; it is a subsheaf precisely by the local
character of a Grothendieck topology.  Each `f⁻¹(A i)` maps to `S`, so by adjunction each
`A i` maps to `f_* S`; the sections of `f_* S` are subsingletons because `f_*`, being a right
adjoint, preserves the monomorphism `S ⟶ ⊤` and the terminal object.  Joint local
inhabitedness on the target and the sheaf condition for `f_* S` then give `f_* S` a section
over *every* object, hence a morphism `⊤ ⟶ f_* S`, whose adjunct is a section of `S` over
every object of the source site — which is the assertion to be proved.  Only left exactness
of `f⁻¹` (through `⊤ ≅ f⁻¹⊤`) and the adjunction are used.

## Main definitions

* `Stacks.Topos.inhabitedSieve`: the sieve on an object of the objects above it carrying a
  section of some member of the family.
* `Stacks.Topos.JointlyLocallyInhabited`: the property that every `inhabitedSieve` is
  covering.
* `Stacks.Topos.inhabitedSheaf`: the subsheaf of the terminal sheaf cut out by that property,
  with its inclusion `Stacks.Topos.inhabitedSheafι` and the maps
  `Stacks.Topos.toInhabitedSheaf` from the members of the family.

## Main results

* `Stacks.Topos.jointlyLocallyInhabited_inverseImage`: the inverse image of a jointly locally
  inhabited family along a morphism of topoi is jointly locally inhabited.
* `Stacks.Topos.exists_cover_inverseImage_sections`: the same conclusion as a covering of each
  object of the source site by objects carrying a section of some `f⁻¹(A i)`.
* `Stacks.Topos.jointlyLocallyInhabited_singleton`: a one-member family is jointly locally
  inhabited as soon as `G ⟶ ⊤` is locally surjective.

## Implementation notes

**Universes.** The two sites, their homs and the two section universes `w` and `w'` of the
two topoi are independent, and the index type `ι` of the family is in its own universe:
nothing here constrains them, because the proof never forms a colimit indexed by `ι`.

**The subsheaf is built as a `Subfunctor` of the terminal sheaf, not as a sheaf of
propositions.** `Subfunctor.isSheaf_iff` reduces its sheaf condition to exactly
`GrothendieckTopology.transitive`, and the ambient terminal sheaf supplies the separatedness
that makes every naturality square and every compatibility condition below a
`Subsingleton.elim`.

**Monomorphy of `f_* (S ⟶ ⊤)` is proved from the adjunction rather than quoted.** What is
needed is only that `Hom (Z, f_* S) → Hom (Z, f_* ⊤)` is injective, which transposes to
`Hom (f⁻¹Z, S) → Hom (f⁻¹Z, ⊤)` and so follows from `S ⟶ ⊤` being a monomorphism.

## References

* [Stacks Project, Tag 00XA](https://stacks.math.columbia.edu/tag/00XA)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Topos

universe v u v' u' w w'

section Inhabited

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {ι : Type*}

/-- The sieve on `U` of objects admitting a section of some member of a family of sheaves. -/
def inhabitedSieve (A : ι → Sheaf J (Type w)) (U : C) : Sieve U where
  arrows V _ := ∃ i, Nonempty ((A i).obj.obj (Opposite.op V))
  downward_closed := by
    rintro V W g ⟨i, ⟨x⟩⟩ h
    exact ⟨i, ⟨(A i).obj.map h.op x⟩⟩

/-- A family of sheaves of types is *jointly locally inhabited* if every object of the site is
covered by objects admitting a section of some member of the family. -/
def JointlyLocallyInhabited (A : ι → Sheaf J (Type w)) : Prop :=
  ∀ U : C, inhabitedSieve J A U ∈ J U

/-- The sieve `inhabitedSieve J A U` is covering as soon as some member of the family has a
section over `U`. -/
theorem inhabitedSieve_mem_of_nonempty {A : ι → Sheaf J (Type w)} {U : C} {i : ι}
    (x : (A i).obj.obj (Opposite.op U)) : inhabitedSieve J A U ∈ J U :=
  J.superset_covering (fun _ h _ => ⟨i, ⟨(A i).obj.map h.op x⟩⟩) (J.top_mem U)

/-- For `g : V ⟶ U`, the sieve `inhabitedSieve J A V` is contained in the pullback along `g` of
`inhabitedSieve J A U`. -/
theorem inhabitedSieve_le_pullback {A : ι → Sheaf J (Type w)} {U V : C} (g : V ⟶ U) :
    inhabitedSieve J A V ≤ (inhabitedSieve J A U).pullback g :=
  fun _ _ h => h

/-- The sections of the terminal sheaf of types over any object form a singleton. -/
private theorem nonempty_unique_terminal_sections (U : Cᵒᵖ) :
    Nonempty (Unique ((⊤_ (Sheaf J (Type w))).obj.obj U)) :=
  ⟨Types.isTerminalEquivUnique _ (terminalIsTerminal.isTerminalObj
    (sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj U))⟩

/-- The sections of the terminal sheaf of types over any object form a subsingleton. -/
theorem subsingleton_terminal_sections (U : Cᵒᵖ) :
    Subsingleton ((⊤_ (Sheaf J (Type w))).obj.obj U) := by
  let _ := (nonempty_unique_terminal_sections J U).some
  infer_instance

/-- The terminal sheaf of types has a section over every object. -/
theorem nonempty_terminal_sections (U : Cᵒᵖ) :
    Nonempty ((⊤_ (Sheaf J (Type w))).obj.obj U) := by
  let _ := (nonempty_unique_terminal_sections J U).some
  infer_instance

/-- A one-member family is jointly locally inhabited as soon as the morphism from its member
to the terminal sheaf is locally surjective. -/
theorem jointlyLocallyInhabited_singleton {G : Sheaf J (Type w)}
    (hG : Sheaf.IsLocallySurjective (terminal.from G)) :
    JointlyLocallyInhabited J (fun _ : PUnit => G) := by
  intro U
  let _ := hG
  refine J.superset_covering ?_
    (Presheaf.imageSieve_mem J (terminal.from G).hom
      (nonempty_terminal_sections J (Opposite.op U)).some)
  rintro V g ⟨p, -⟩
  exact ⟨PUnit.unit, ⟨p⟩⟩

/-- The subfunctor of the terminal sheaf whose sections over `U` record that `U` is covered by
objects admitting a section of some member of the family. -/
def inhabitedSubfunctor (A : ι → Sheaf J (Type w)) :
    Subfunctor (⊤_ (Sheaf J (Type w))).obj where
  obj U := {_x | inhabitedSieve J A U.unop ∈ J U.unop}
  map g _ h := J.superset_covering (inhabitedSieve_le_pullback J g.unop)
    (J.pullback_stable g.unop h)

/-- The subfunctor `inhabitedSubfunctor J A` of the terminal sheaf satisfies the sheaf
condition. -/
theorem inhabitedSubfunctor_isSheaf (A : ι → Sheaf J (Type w)) :
    Presieve.IsSheaf J (inhabitedSubfunctor J A).toFunctor :=
  (Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type J _).1
    (⊤_ (Sheaf J (Type w))).property)).2 fun _ _ hs =>
      J.transitive hs _ fun _ g hg => J.superset_covering (inhabitedSieve_le_pullback J g) hg

/-- The subsheaf of the terminal sheaf cut out by `JointlyLocallyInhabited`. -/
noncomputable def inhabitedSheaf (A : ι → Sheaf J (Type w)) : Sheaf J (Type w) :=
  ⟨(inhabitedSubfunctor J A).toFunctor,
    (isSheaf_iff_isSheaf_of_type J _).2 (inhabitedSubfunctor_isSheaf J A)⟩

/-- The inclusion of `inhabitedSheaf` into the terminal sheaf. -/
noncomputable def inhabitedSheafι (A : ι → Sheaf J (Type w)) :
    inhabitedSheaf J A ⟶ ⊤_ (Sheaf J (Type w)) :=
  ⟨(inhabitedSubfunctor J A).ι⟩

/-- The inclusion `inhabitedSheafι J A` of `inhabitedSheaf J A` into the terminal sheaf is a
monomorphism. -/
instance inhabitedSheafι_mono (A : ι → Sheaf J (Type w)) : Mono (inhabitedSheafι J A) := by
  let _ : ∀ U : Cᵒᵖ, Mono (((sheafToPresheaf J (Type w)).map (inhabitedSheafι J A)).app U) :=
    fun _ => by rw [CategoryTheory.mono_iff_injective]; exact Subtype.val_injective
  exact (sheafToPresheaf J (Type w)).mono_of_mono_map (NatTrans.mono_of_mono_app _)

/-- The sections of `inhabitedSheaf J A` over any object form a subsingleton. -/
instance subsingleton_inhabitedSheaf_sections (A : ι → Sheaf J (Type w)) (U : Cᵒᵖ) :
    Subsingleton ((inhabitedSheaf J A).obj.obj U) :=
  ⟨fun _ _ => Subtype.ext ((subsingleton_terminal_sections J U).elim _ _)⟩

/-- Each member of the family maps to the subsheaf of the terminal sheaf that it inhabits. -/
noncomputable def toInhabitedSheaf (A : ι → Sheaf J (Type w)) (i : ι) :
    A i ⟶ inhabitedSheaf J A where
  hom :=
    { app := fun U => ↾(fun p => ⟨(terminal.from (A i)).hom.app U p,
        inhabitedSieve_mem_of_nonempty J p⟩)
      naturality := by intro U V g; ext p; exact Subsingleton.elim _ _ }

end Inhabited

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D} {ι : Type*}

/-- **The inverse image of a jointly locally inhabited family is jointly locally inhabited.**
If every object of the target site is covered by objects carrying a section of some member of
a family `A` of sheaves of types, then every object of the source site is covered by objects
carrying a section of some `f⁻¹(A i)`.

No coproduct is formed over the index type, so nothing is assumed about the existence of
colimits in either category of sheaves of types; see the module documentation. -/
theorem jointlyLocallyInhabited_inverseImage
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
    (A : ι → Sheaf K (Type w')) (hA : JointlyLocallyInhabited K A) :
    JointlyLocallyInhabited J (fun i => f.inverseImage.obj (A i)) := by
  let _ := f.preservesFiniteLimits
  let _ := f.adj.rightAdjoint_preservesLimits
  let B : ι → Sheaf J (Type w) := fun i => f.inverseImage.obj (A i)
  let S := inhabitedSheaf J B
  let ι₀ : S ⟶ ⊤_ (Sheaf J (Type w)) := inhabitedSheafι J B
  have hfrom : terminal.from (f.pushforward.obj (⊤_ (Sheaf J (Type w)))) =
      terminalComparison f.pushforward := terminalIsTerminal.hom_ext _ _
  have hcomp : terminal.from (f.pushforward.obj S) =
      f.pushforward.map ι₀ ≫ terminal.from (f.pushforward.obj (⊤_ (Sheaf J (Type w)))) :=
    terminalIsTerminal.hom_ext _ _
  have hmono : Mono (f.pushforward.map ι₀) := by
    constructor
    intro Z a b hab
    apply (f.adj.homEquiv Z S).symm.injective
    apply (cancel_mono ι₀).mp
    rw [← Adjunction.homEquiv_naturality_right_symm,
      ← Adjunction.homEquiv_naturality_right_symm, hab]
  have hmono' : Mono (terminal.from (f.pushforward.obj S)) := by
    rw [hcomp, hfrom]
    infer_instance
  have hsub : ∀ W : Dᵒᵖ, Subsingleton ((f.pushforward.obj S).obj.obj W) := by
    intro W
    have h₁ : Mono (terminal.from (f.pushforward.obj S)).hom :=
      inferInstanceAs (Mono ((sheafToPresheaf K (Type w')).map
        (terminal.from (f.pushforward.obj S))))
    have h₂ : Mono ((terminal.from (f.pushforward.obj S)).hom.app W) :=
      inferInstanceAs (Mono (((evaluation Dᵒᵖ (Type w')).obj W).map
        (terminal.from (f.pushforward.obj S)).hom))
    let _ := subsingleton_terminal_sections K W
    exact ((CategoryTheory.mono_iff_injective _).mp h₂).subsingleton
  have hne : ∀ W : Dᵒᵖ, Nonempty ((f.pushforward.obj S).obj.obj W) := by
    intro W
    have hstep : ∀ (V : D) (_ : V ⟶ W.unop), (∃ i, Nonempty ((A i).obj.obj (Opposite.op V))) →
        Nonempty ((f.pushforward.obj S).obj.obj (Opposite.op V)) := by
      rintro V _ ⟨i, ⟨x⟩⟩
      exact ⟨(f.adj.homEquiv (A i) S (toInhabitedSheaf J B i)).hom.app (Opposite.op V) x⟩
    have hsheaf := (isSheaf_iff_isSheaf_of_type K _).1 (f.pushforward.obj S).property
    let x : Presieve.FamilyOfElements (f.pushforward.obj S).obj
        (inhabitedSieve K A W.unop).arrows :=
      fun V g hg => (hstep V g hg).some
    have hx : x.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ h₁ h₂ hh₁ hh₂ _
      exact (hsub (Opposite.op Z)).elim _ _
    exact ⟨(hsheaf _ (hA W.unop)).amalgamate x hx⟩
  let t : ⊤_ (Sheaf K (Type w')) ⟶ f.pushforward.obj S :=
    ⟨{ app := fun W => ↾(fun _ => (hne W).some)
       naturality := by intro U V g; ext p; exact (hsub V).elim _ _ }⟩
  let τ : ⊤_ (Sheaf J (Type w)) ⟶ S :=
    inv (terminalComparison f.inverseImage) ≫ (f.adj.homEquiv _ S).symm t
  intro U
  exact (τ.hom.app (Opposite.op U) (nonempty_terminal_sections J (Opposite.op U)).some).2

/-- **The source cover.** The covering form of `jointlyLocallyInhabited_inverseImage`: every
object of the source site has a covering whose members carry a section of the inverse image of
some member of the family. -/
theorem exists_cover_inverseImage_sections
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
    (A : ι → Sheaf K (Type w')) (hA : JointlyLocallyInhabited K A) (U : C) :
    ∃ T : J.Cover U, ∀ (V : C) (g : V ⟶ U), T g →
      ∃ i, Nonempty ((f.inverseImage.obj (A i)).obj.obj (Opposite.op V)) :=
  ⟨⟨inhabitedSieve J (fun i => f.inverseImage.obj (A i)) U,
    jointlyLocallyInhabited_inverseImage f A hA U⟩, fun _ _ hg => hg⟩

end Transport

end Stacks.Topos

end
