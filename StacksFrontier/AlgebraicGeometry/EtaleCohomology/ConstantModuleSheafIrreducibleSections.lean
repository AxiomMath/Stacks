module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocallyConstantCompactSupport
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantSheafLocalSections

/-!
# Global sections of a constant sheaf of modules on the small étale site

Let `(C, J)` be a site, let `Λ` be a commutative ring and let `M` be a `Λ`-module. The canonical
map `θ_X : M ⟶ Γ(X, M̲)` from `M` to the sections over `X` of the constant sheaf it generates is
injective as soon as `X` is not sheaf theoretically empty, that is, as soon as the empty sieve
does not cover `X`: two constants with the same image agree on a covering family of `X`, and the
restriction maps of the constant *presheaf* are the identity, so the agreement is an equality in
`M` provided that covering family has a member.

When `X` is moreover final, `θ_X` is the unit of the constant sheaf adjunction, and it is then
*surjective* as well provided any two objects which are not sheaf theoretically empty admit a
common refinement which is not sheaf theoretically empty either: a section over `X` is locally a
constant, and that refinement property forces the local constants to agree.

On the small étale site of a scheme `W` the final object is not sheaf theoretically empty exactly
when `W` has a point, and two objects which are not sheaf theoretically empty are refined by
their fibre product, whose underlying scheme has a point because the structure morphisms are
étale, hence open, so their images are nonempty opens of `W` and meet when `W` is irreducible.
So on the small étale site of an irreducible scheme the unit `θ_W : M ⟶ Γ(W, M̲)` is an
isomorphism: the global sections of a constant sheaf of modules are the constants.

## Main results

* `Stacks.ConstantSheaf.injective_toSheafify_const_app_of_not_bot_mem` and
  `Stacks.ConstantSheaf.injective_constantSheafAdj_unit_app_of_not_bot_mem`: on an arbitrary site
  the canonical map from a module to the sections of the constant sheaf over an object which is
  not sheaf theoretically empty is injective, in the two shapes it is met in — as the
  sheafification map of the constant presheaf read off at that object, and, when the object is
  final, as the unit of the constant sheaf adjunction.
* `Stacks.ConstantSheaf.surjective_toSheafify_const_app_of_forall_exists_refinement` and
  `Stacks.ConstantSheaf.bijective_toSheafify_const_app_of_forall_exists_refinement`: the same map
  over a final object is surjective, hence bijective, when objects which are not sheaf
  theoretically empty admit common refinements of the same kind.
* `AlgebraicGeometry.SmallEtale.not_bot_mem_topology_final`: the final object of the small étale
  site of a nonempty scheme is not sheaf theoretically empty.
* `AlgebraicGeometry.SmallEtale.exists_refinement_not_bot_mem_of_irreducibleSpace`: on the small
  étale site of an irreducible scheme the refinement property holds, by fibre products.
* `AlgebraicGeometry.SmallEtale.injective_constantModuleSheafUnit_final` and
  `AlgebraicGeometry.SmallEtale.mono_constantModuleSheafUnit_final`: the unit
  `θ_W : M ⟶ Γ(W, M̲)` on the small étale site of an irreducible scheme is injective, resp. a
  monomorphism of `Λ`-modules.
* `AlgebraicGeometry.SmallEtale.bijective_constantModuleSheafUnit_final`,
  `AlgebraicGeometry.SmallEtale.isIso_constantModuleSheafUnit_final` and
  `AlgebraicGeometry.SmallEtale.constantModuleSheafSectionsIsoFinal`: that unit is in fact an
  isomorphism `M ≅ Γ(W, M̲)`.

## Implementation notes

*What irreducibility is used for.* Injectivity of `θ_W` uses only that `W` has a point: it is a
statement about one object of the site, and the covering family produced by local injectivity of
sheafification already consists of objects on which the two constants are equal. Irreducibility
enters in surjectivity, where two members of the covering family produced by local surjectivity
have to be compared on a common refinement which is again not sheaf theoretically empty.
Accordingly the site-level statements are given with the sheaf theoretic hypotheses the argument
consumes — `(⊥ : Sieve X) ∉ J X` and the refinement property — and the étale statements are given
for `W` irreducible, which is the form they are used in. No hypothesis on `Λ` beyond being a
commutative ring is needed; in particular it need not be Noetherian.

*The sheaf theoretic emptiness of the final object.* `(⊥ : Sieve X) ∈ J X` is the sheaf theoretic
meaning of `X` being empty, and on the small étale site it is equivalent to the underlying scheme
of `X` being empty:
`Stacks.EtaleCohomology.bot_mem_topology` and
`Stacks.EtaleCohomology.not_bot_mem_smallEtaleTopology`. The underlying scheme of the final
object `SmallEtale.final` is `W` itself, so a point of `W` is all that is required.

*The fibre product is taken in the site.* The small étale site has fibre products and the functor
to schemes preserves them, so the underlying scheme of the fibre product of two objects is the
fibre product of their underlying schemes; `AlgebraicGeometry.Scheme.isEmpty_pullback_iff` then
turns having a point into the images of the two structure morphisms not being disjoint.

*The universes.* The site `SmallEtale B W hW` is a `Type (u + 1)` with `Type u` homs, so the
module universe `max u v w` of the site-level statements is `max (u + 1) u w`; it is `u + 1` for
`Λ : Type (u + 1)`, which is the coefficient universe the constructibility results on this site
are stated at.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace Stacks.ConstantSheaf

section Site

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {Λ : Type w} [CommRing Λ]
  [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]

/-- A covering family indexed by an empty type generates the empty sieve, so its target is sheaf
theoretically empty. -/
private theorem bot_mem_of_ofArrows_mem_of_isEmpty {X : C} {I : Type*} [IsEmpty I]
    (U : I → C) (f : ∀ i, U i ⟶ X) (hcov : Sieve.ofArrows U f ∈ J X) :
    (⊥ : Sieve X) ∈ J X := by
  have hbot : Sieve.ofArrows U f = ⊥ := by
    refine le_antisymm (fun Z g hg => ?_) bot_le
    obtain ⟨Y, h, g', hg', -⟩ := hg
    cases hg' with
    | mk i => exact (IsEmpty.false i).elim
  rwa [hbot] at hcov

/-- **The canonical map from a module to the sections of the constant sheaf it generates is
injective over an object which is not sheaf theoretically empty.**

Two constants with the same image agree on a covering family of the object, by local injectivity
of sheafification; the restriction maps of the constant presheaf are the identity, so on each
member of that family the agreement is an equality in the module itself. The family therefore has
no member only if the empty sieve covers the object. -/
theorem injective_toSheafify_const_app_of_not_bot_mem (M : ModuleCat.{max u v w} Λ) (X : C)
    (hX : (⊥ : Sieve X) ∉ J X) :
    Function.Injective ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op X)) := by
  intro x y hxy
  obtain ⟨I, U, f, hcov, heq⟩ := exists_cover_eq_constant_sections J M X x y hxy
  rcases isEmpty_or_nonempty I with hI | hI
  · exact absurd (bot_mem_of_ofArrows_mem_of_isEmpty J U f hcov) hX
  · exact heq hI.some

/-- **The unit of the constant sheaf adjunction on modules is injective at a final object which
is not sheaf theoretically empty.** The unit is the sheafification map of the constant presheaf
read off at the final object, so this is
`Stacks.ConstantSheaf.injective_toSheafify_const_app_of_not_bot_mem`. -/
theorem injective_constantSheafAdj_unit_app_of_not_bot_mem {T : C} (hT : IsTerminal T)
    (hbot : (⊥ : Sieve T) ∉ J T) (M : ModuleCat.{max u v w} Λ) :
    Function.Injective
      ((constantSheafAdj J (ModuleCat.{max u v w} Λ) hT).unit.app M) := by
  rw [constantSheafAdj_unit_app J (ModuleCat.{max u v w} Λ) hT M]
  exact injective_toSheafify_const_app_of_not_bot_mem J M T hbot

end Site

section Surjective

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {Λ : Type w} [CommRing Λ]

/-- The sections of the sheafified constant presheaf of `Λ`-modules satisfy the sheaf condition
for presheaves of types. -/
private theorem isSheaf_forget_sheafify_const (M : ModuleCat.{max u v w} Λ) :
    Presieve.IsSheaf J
      (sheafify J ((Functor.const Cᵒᵖ).obj M) ⋙ forget (ModuleCat.{max u v w} Λ)) := by
  have := preservesSheafification_forget_moduleCat.{v, u, w} J Λ
  exact (isSheaf_iff_isSheaf_of_type _ _).1
    (GrothendieckTopology.HasSheafCompose.isSheaf _
      ((presheafToSheaf J (ModuleCat.{max u v w} Λ)).obj
        ((Functor.const Cᵒᵖ).obj M)).property)

/-- A covering sieve all of whose members are sheaf theoretically empty has sheaf theoretically
empty target. -/
private theorem bot_mem_of_forall_bot_mem {X : C} {S : Sieve X} (hS : S ∈ J X)
    (h : ∀ (Y : C) (g : Y ⟶ X), S g → (⊥ : Sieve Y) ∈ J Y) :
    (⊥ : Sieve X) ∈ J X := by
  refine J.transitive hS ⊥ fun {Y} g hg => ?_
  have h0 : (⊥ : Sieve X).pullback g = ⊥ := le_antisymm (fun _ k hk => hk) bot_le
  rw [h0]
  exact h Y g hg

/-- **The sections of a constant sheaf of modules over a final object are the constants, when any
two objects which are not sheaf theoretically empty have a common refinement which is not sheaf
theoretically empty either.**

Sheafification is locally surjective, so a section over the final object is a constant on a
covering family. Any member of that family which is not sheaf theoretically empty exhibits the
same constant: two members are compared on a common refinement, where the two constants have the
same image and hence agree by
`Stacks.ConstantSheaf.injective_toSheafify_const_app_of_not_bot_mem`. On a member which *is*
sheaf theoretically empty the sections form a singleton, so there is nothing to check, and the
sheaf condition then identifies the section with that one constant. -/
theorem surjective_toSheafify_const_app_of_forall_exists_refinement
    (M : ModuleCat.{max u v w} Λ) {T : C} (hT : IsTerminal T) (hbot : (⊥ : Sieve T) ∉ J T)
    (href : ∀ Y Z : C, (⊥ : Sieve Y) ∉ J Y → (⊥ : Sieve Z) ∉ J Z →
      ∃ (Q : C) (_ : Q ⟶ Y) (_ : Q ⟶ Z), (⊥ : Sieve Q) ∉ J Q) :
    Function.Surjective ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T)) := by
  classical
  intro s
  have hls := isLocallySurjective_toSheafify_moduleCat.{v, u, w} J Λ ((Functor.const Cᵒᵖ).obj M)
  have hsheaf := isSheaf_forget_sheafify_const J M
  have hS : Presheaf.imageSieve (toSheafify J ((Functor.const Cᵒᵖ).obj M)) s ∈ J T :=
    Presheaf.imageSieve_mem J _ s
  have hex : ∃ (Y : C) (g : Y ⟶ T),
      Presheaf.imageSieve (toSheafify J ((Functor.const Cᵒᵖ).obj M)) s g ∧
        (⊥ : Sieve Y) ∉ J Y := by
    by_contra hcon
    exact hbot (bot_mem_of_forall_bot_mem J hS fun Y g hg =>
      of_not_not fun hY => hcon ⟨Y, g, hg, hY⟩)
  obtain ⟨Y₀, g₀, ⟨a₀, ha₀⟩, hY₀⟩ := hex
  refine ⟨a₀, (hsheaf _ hS).isSeparatedFor.ext fun {Y} g hg => ?_⟩
  have hres : ∀ {Z Y' : C} (k : Z ⟶ Y') (v : M),
      (sheafify J ((Functor.const Cᵒᵖ).obj M)).map k.op
          ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op Y') v) =
        (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op Z) v :=
    fun k v => (NatTrans.naturality_apply (toSheafify J ((Functor.const Cᵒᵖ).obj M)) k.op v).symm
  have hres_eq : ∀ {Z Y' : C} (k : Z ⟶ Y') (g' : Y' ⟶ T) (v : M),
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op Y') v =
          (sheafify J ((Functor.const Cᵒᵖ).obj M)).map g'.op s →
        (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op Z) v =
          (sheafify J ((Functor.const Cᵒᵖ).obj M)).map (k ≫ g').op s := fun k g' v h => by
    rw [← hres k v, h, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  show (sheafify J ((Functor.const Cᵒᵖ).obj M)).map g.op
      ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) a₀) = _
  rw [hres g a₀]
  obtain ⟨a, ha⟩ := hg
  by_cases hY : (⊥ : Sieve Y) ∈ J Y
  · exact (hsheaf ⊥ hY).isSeparatedFor.ext fun _ _ h => h.elim
  obtain ⟨Q, q, r, hQ⟩ := href Y Y₀ hY hY₀
  have hcomm : q ≫ g = r ≫ g₀ := hT.hom_ext _ _
  have hvv : a = a₀ :=
    injective_toSheafify_const_app_of_not_bot_mem J M Q hQ
      (by rw [hres_eq q g a ha, hres_eq r g₀ a₀ ha₀, hcomm])
  rw [← hvv]
  exact ha

/-- **The sections of a constant sheaf of modules over a final object are exactly the
constants**, under the hypotheses of
`Stacks.ConstantSheaf.surjective_toSheafify_const_app_of_forall_exists_refinement`. -/
theorem bijective_toSheafify_const_app_of_forall_exists_refinement
    (M : ModuleCat.{max u v w} Λ) {T : C} (hT : IsTerminal T) (hbot : (⊥ : Sieve T) ∉ J T)
    (href : ∀ Y Z : C, (⊥ : Sieve Y) ∉ J Y → (⊥ : Sieve Z) ∉ J Z →
      ∃ (Q : C) (_ : Q ⟶ Y) (_ : Q ⟶ Z), (⊥ : Sieve Q) ∉ J Q) :
    Function.Bijective ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T)) :=
  ⟨injective_toSheafify_const_app_of_not_bot_mem J M T hbot,
    surjective_toSheafify_const_app_of_forall_exists_refinement J M hT hbot href⟩

end Surjective

end Stacks.ConstantSheaf

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (W : Scheme.{u}) (hW : B.Contains W)

/-- The final object of the small étale site of a scheme with a point is not sheaf theoretically
empty: the underlying scheme of that final object is `W` itself, so a point of it is exactly a
point of `W`.

The point is taken as an explicit argument rather than as a `Nonempty` instance: the hypothesis
is genuinely necessary — over an empty `W` the empty sieve *does* cover — and naming the witness
keeps that visible at every use site. -/
theorem not_bot_mem_topology_final
    (w : (SmallEtale.toScheme B W hW).obj (SmallEtale.final B W hW)) :
    (⊥ : Sieve (SmallEtale.final B W hW)) ∉
      SmallEtale.topology B W hW (SmallEtale.final B W hW) :=
  Stacks.EtaleCohomology.not_bot_mem_smallEtaleTopology B W hW w

/-- **On the small étale site of an irreducible scheme any two objects which are not sheaf
theoretically empty are refined by a common object which is not sheaf theoretically empty
either**, namely their fibre product over the final object. Its underlying scheme is the fibre
product of the underlying schemes, which has a point because the two structure morphisms are
étale, hence open, so their images are nonempty opens of the irreducible `W` and therefore
meet. -/
theorem exists_refinement_not_bot_mem_of_irreducibleSpace [IrreducibleSpace W]
    (Y Z : SmallEtale B W hW) (hY : (⊥ : Sieve Y) ∉ SmallEtale.topology B W hW Y)
    (hZ : (⊥ : Sieve Z) ∉ SmallEtale.topology B W hW Z) :
    ∃ (Q : SmallEtale B W hW) (_ : Q ⟶ Y) (_ : Q ⟶ Z),
      (⊥ : Sieve Q) ∉ SmallEtale.topology B W hW Q := by
  obtain ⟨y⟩ := Stacks.EtaleCohomology.nonempty_of_not_bot_mem_smallEtaleTopology B W hW hY
  obtain ⟨z⟩ := Stacks.EtaleCohomology.nonempty_of_not_bot_mem_smallEtaleTopology B W hW hZ
  let F := SmallEtale.toScheme B W hW
  let cY := (SmallEtale.finalIsTerminal B W hW).from Y
  let cZ := (SmallEtale.finalIsTerminal B W hW).from Z
  have hopen : ∀ X : SmallEtale B W hW,
      IsOpen (Set.range (F.map ((SmallEtale.finalIsTerminal B W hW).from X)).base) := fun X =>
    (B.inclusion.map X.obj.hom).isOpenMap.isOpen_range
  have hirr : PreirreducibleSpace (F.obj (SmallEtale.final B W hW)) :=
    inferInstanceAs (PreirreducibleSpace W)
  obtain ⟨t, ht⟩ := nonempty_preirreducible_inter (hopen Y) (hopen Z)
    ⟨(F.map cY).base y, y, rfl⟩ ⟨(F.map cZ).base z, z, rfl⟩
  have hne : Nonempty ↑(Limits.pullback (F.map cY) (F.map cZ)) := by
    rw [← not_isEmpty_iff, AlgebraicGeometry.Scheme.isEmpty_pullback_iff, Set.not_disjoint_iff]
    exact ⟨t, ht.1, ht.2⟩
  exact ⟨Limits.pullback cY cZ, Limits.pullback.fst cY cZ, Limits.pullback.snd cY cZ,
    Stacks.EtaleCohomology.not_bot_mem_smallEtaleTopology B W hW
      ((Limits.PreservesPullback.iso F cY cZ).inv.base hne.some)⟩

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The unit of the constant sheaf of `Λ`-modules on the small étale site of an irreducible
scheme is injective.** A global section of the constant sheaf determines the constant it comes
from: two constants with the same image agree on a covering family of the final object, and that
family is nonempty because `W` has a point.

Injectivity alone needs no more than `Nonempty W`; irreducibility is what makes the unit
*surjective* as well, in
`AlgebraicGeometry.SmallEtale.bijective_constantModuleSheafUnit_final`. -/
theorem injective_constantModuleSheafUnit_final [IrreducibleSpace W]
    (M : ModuleCat.{u + 1} Λ) :
    Function.Injective
      ((constantSheafAdj (SmallEtale.topology B W hW) (ModuleCat.{u + 1} Λ)
        (SmallEtale.finalIsTerminal B W hW)).unit.app M) :=
  Stacks.ConstantSheaf.injective_constantSheafAdj_unit_app_of_not_bot_mem.{u, u + 1, u + 1}
    (SmallEtale.topology B W hW) (SmallEtale.finalIsTerminal B W hW)
    (not_bot_mem_topology_final B W hW
      (show (SmallEtale.toScheme B W hW).obj (SmallEtale.final B W hW) from
        Nonempty.some (inferInstanceAs (Nonempty W)))) M

/-- **The unit of the constant sheaf of `Λ`-modules on the small étale site of an irreducible
scheme is a monomorphism of `Λ`-modules**, which is
`AlgebraicGeometry.SmallEtale.injective_constantModuleSheafUnit_final` read categorically. -/
theorem mono_constantModuleSheafUnit_final [IrreducibleSpace W] (M : ModuleCat.{u + 1} Λ) :
    Mono ((constantSheafAdj (SmallEtale.topology B W hW) (ModuleCat.{u + 1} Λ)
      (SmallEtale.finalIsTerminal B W hW)).unit.app M) :=
  (ModuleCat.mono_iff_injective _).2 (injective_constantModuleSheafUnit_final B W hW Λ M)

/-- **The global sections of the constant sheaf of `Λ`-modules on the small étale site of an
irreducible scheme are exactly the constants.** Sheafification is locally surjective, so a global
section is a constant on a covering family of the final object; two members of that family which
are not sheaf theoretically empty are compared on their fibre product, which is not sheaf
theoretically empty because `W` is irreducible, so they carry the same constant; and on a member
which is sheaf theoretically empty there is only one section. -/
theorem bijective_constantModuleSheafUnit_final [IrreducibleSpace W]
    (M : ModuleCat.{u + 1} Λ) :
    Function.Bijective
      ((constantSheafAdj (SmallEtale.topology B W hW) (ModuleCat.{u + 1} Λ)
        (SmallEtale.finalIsTerminal B W hW)).unit.app M) := by
  rw [Stacks.ConstantSheaf.constantSheafAdj_unit_app (SmallEtale.topology B W hW)
    (ModuleCat.{u + 1} Λ) (SmallEtale.finalIsTerminal B W hW) M]
  exact Stacks.ConstantSheaf.bijective_toSheafify_const_app_of_forall_exists_refinement.{u, u + 1,
    u + 1} (SmallEtale.topology B W hW) M (SmallEtale.finalIsTerminal B W hW)
    (not_bot_mem_topology_final B W hW
      (show (SmallEtale.toScheme B W hW).obj (SmallEtale.final B W hW) from
        Nonempty.some (inferInstanceAs (Nonempty W))))
    (exists_refinement_not_bot_mem_of_irreducibleSpace B W hW)

/-- **The unit of the constant sheaf of `Λ`-modules on the small étale site of an irreducible
scheme is an isomorphism**, which is
`AlgebraicGeometry.SmallEtale.bijective_constantModuleSheafUnit_final` read categorically. -/
theorem isIso_constantModuleSheafUnit_final [IrreducibleSpace W] (M : ModuleCat.{u + 1} Λ) :
    IsIso ((constantSheafAdj (SmallEtale.topology B W hW) (ModuleCat.{u + 1} Λ)
      (SmallEtale.finalIsTerminal B W hW)).unit.app M) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_constantModuleSheafUnit_final B W hW Λ M)

/-- **The constant sheaf of `Λ`-modules on the small étale site of an irreducible scheme has the
module itself as its global sections**, by the unit of the constant sheaf adjunction. -/
def constantModuleSheafSectionsIsoFinal [IrreducibleSpace W] (M : ModuleCat.{u + 1} Λ) :
    M ≅ ((constantSheaf (SmallEtale.topology B W hW) (ModuleCat.{u + 1} Λ)).obj M).obj.obj
      (op (SmallEtale.final B W hW)) :=
  have := isIso_constantModuleSheafUnit_final B W hW Λ M
  asIso ((constantSheafAdj (SmallEtale.topology B W hW) (ModuleCat.{u + 1} Λ)
    (SmallEtale.finalIsTerminal B W hW)).unit.app M)

end AlgebraicGeometry.SmallEtale

end
