module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreSets.OverPullbackLimits
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constant sheaves of sets and global sections, on a site with no final object

Let `(C, J)` and `(D, K)` be small sites and let `L ⊣ R` be an adjoint pair between their topoi
of sheaves of sets, with `L : Sh(D) ⥤ Sh(C)` left exact. Then `L` carries the constant sheaf on
a set to the constant sheaf on that set
(`Stacks.ConstantSheaf.inverseImageConstantSheafIsoOfSmallSites`), with **no final object
assumed in either site**.

This is `Stacks.ConstantSheaf.inverseImageConstantSheafIso` with its two hypotheses
`IsTerminal T`, `IsTerminal T'` removed. Those are there because that proof identifies the
right adjoint of the constant sheaf functor with sections over a final object of the site,
which presupposes one. The identification used here instead is Mathlib's global sections
functor `CategoryTheory.Sheaf.Γ`, *defined* as the right adjoint of the constant sheaf functor
and available on every site whose coefficient category has limits of shape `Cᵒᵖ`
(`CategoryTheory.hasGlobalSectionsFunctor_of_hasLimitsOfShape`). For sheaves of sets it is
corepresented by the terminal sheaf (`CategoryTheory.Sheaf.ΓNatIsoCoyoneda`), and the terminal
sheaf is the one object a topos always has whether or not its site does: so
`R` followed by global sections on `D` is global sections on `C` as soon as `L` carries the
terminal sheaf to the terminal sheaf, which left exactness gives. Uniqueness of left adjoints
then compares `constantSheaf K ⋙ L` with `constantSheaf J`.

The terminal sheaf is presented here as the constant sheaf on a singleton, which is what
corepresents global sections; that it is terminal is
`Stacks.ConstantSheaf.isTerminal_constantSheafPUnit`, proved from the fact that the constant
presheaf on a singleton is a sheaf and that sheafifying a sheaf changes nothing.

## Main definitions

* `Stacks.ConstantSheaf.punitSheaf` — the sheaf of singletons, i.e. the constant presheaf on a
  singleton together with its sheaf condition.
* `Stacks.ConstantSheaf.inverseImageConstantSheafIsoOfSmallSites` — a left exact left adjoint
  between the topoi of sheaves of sets on two small sites commutes with the constant sheaf
  functor.
* `Stacks.ConstantSheaf.overPullbackConstantSheafIsoOfSmallSite` — the case of restriction to an
  object of the site: this is `Stacks.ConstantSheaf.overPullbackConstantSheafIsoType` with its
  final-object hypothesis removed, and with the adjoint pair taken to be the continuous and
  cocontinuous functor `Over.forget U` rather than `Over.forget U ⊣ Over.star U`, so that no
  binary products are required in `C` either.

## Main results

* `Stacks.ConstantSheaf.isTerminal_constantSheafPUnit` — the constant sheaf on a singleton is a
  final object of the topos.
* `Stacks.ConstantSheaf.globalSectionsIsoOfAdjunction` — global sections on `D` of `R` are
  global sections on `C`.
* `Stacks.ConstantSheaf.isConstant_obj_of_smallSites` and
  `Stacks.ConstantSheaf.isConstant_overPullback_of_smallSite` — the `Prop`-valued forms.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w

namespace Stacks.ConstantSheaf

/-! ### The sheaf of singletons -/

section PUnit

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)

/-- The constant presheaf on a singleton is a sheaf: every compatible family amalgamates, and
the amalgamation is unique because all of its sections agree. -/
public lemma isSheaf_constPUnit : Presheaf.IsSheaf J ((Functor.const Cᵒᵖ).obj (PUnit.{w + 1})) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro U S hS x hx
  refine ⟨PUnit.unit, ?_, ?_⟩
  · intro V g hg; exact Subsingleton.elim (α := PUnit.{w + 1}) _ _
  · intro y hy; exact Subsingleton.elim (α := PUnit.{w + 1}) _ _

/-- **The sheaf of singletons**: the constant presheaf on a singleton, which is a sheaf by
`Stacks.ConstantSheaf.isSheaf_constPUnit`. -/
public def punitSheaf : Sheaf J (Type w) :=
  ⟨(Functor.const Cᵒᵖ).obj PUnit.{w + 1}, isSheaf_constPUnit J⟩

/-- The sheaf of singletons is a final object of the topos: a morphism into it is determined
objectwise, and there is nothing to choose. -/
public def isTerminal_punitSheaf : IsTerminal (punitSheaf J) :=
  IsTerminal.ofUniqueHom (fun _ => ⟨{ app := fun _ => ↾fun _ => PUnit.unit }⟩)
    (fun _ _ => by ext U z; exact Subsingleton.elim (α := PUnit.{w + 1}) _ _)

/-- **The constant sheaf on a singleton is a final object of the topos.** It is the
sheafification of the sheaf of singletons, and sheafifying a sheaf changes nothing. -/
public def isTerminal_constantSheafPUnit :
    IsTerminal ((constantSheaf J (Type w)).obj PUnit.{w + 1}) :=
  (isTerminal_punitSheaf J).ofIso (sheafificationIso (punitSheaf J))

end PUnit

/-! ### A left exact left adjoint and the constant sheaf functor -/

section Transfer

variable {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {L : Sheaf K (Type w) ⥤ Sheaf J (Type w)} {R : Sheaf J (Type w) ⥤ Sheaf K (Type w)}

/-- A left exact functor carries the constant sheaf on a singleton to the constant sheaf on a
singleton: both are final objects, by
`Stacks.ConstantSheaf.isTerminal_constantSheafPUnit`. -/
public def constantSheafPUnitIsoOfPreservesTerminal (L : Sheaf K (Type w) ⥤ Sheaf J (Type w))
    [PreservesFiniteLimits L] :
    L.obj ((constantSheaf K (Type w)).obj PUnit.{w + 1}) ≅
      (constantSheaf J (Type w)).obj PUnit.{w + 1} :=
  (IsTerminal.isTerminalObj L _ (isTerminal_constantSheafPUnit K)).uniqueUpToIso
    (isTerminal_constantSheafPUnit J)

/-- **Global sections of the right adjoint are global sections.** For an adjoint pair `L ⊣ R`
between the topoi of sheaves of sets on two small sites with `L` left exact, the global sections
on `D` of `R F` are the global sections on `C` of `F`, naturally in `F`.

Global sections of sheaves of sets are corepresented by the constant sheaf on a singleton
(`CategoryTheory.Sheaf.ΓNatIsoCoyoneda`), the adjunction turns a morphism from it into a
morphism from its image under `L` (`CategoryTheory.Adjunction.compCoyonedaIso`), and that image
is again the constant sheaf on a singleton because `L` is left exact. No final object of either
site is used. -/
@[sga "4 IV 4.3" "more general"]
public def globalSectionsIsoOfAdjunction (adj : L ⊣ R) [PreservesFiniteLimits L] :
    R ⋙ Sheaf.Γ K (Type w) ≅ Sheaf.Γ J (Type w) :=
  Functor.isoWhiskerLeft R (Sheaf.ΓNatIsoCoyoneda K PUnit.{w + 1}) ≪≫
    (adj.compCoyonedaIso.app (op ((constantSheaf K (Type w)).obj PUnit.{w + 1}))).symm ≪≫
    coyoneda.mapIso (Iso.op (constantSheafPUnitIsoOfPreservesTerminal L)).symm ≪≫
    (Sheaf.ΓNatIsoCoyoneda J PUnit.{w + 1}).symm

/-- **The inverse image of a constant sheaf of sets is constant, with no final object in either
site.** If `L ⊣ R` are functors between the topoi of sheaves of sets on two small sites and `L`
is left exact, then `L` carries the constant sheaf on a set to the constant sheaf on that set.

Both `constantSheaf K ⋙ L` and `constantSheaf J` are left adjoint to global sections on `C`, the
first by `Stacks.ConstantSheaf.globalSectionsIsoOfAdjunction`, so they agree. This is
`Stacks.ConstantSheaf.inverseImageConstantSheafIso` without its two final-object
hypotheses. -/
@[sga "4 IV 4.3" "more general"]
public def inverseImageConstantSheafIsoOfSmallSites (adj : L ⊣ R) [PreservesFiniteLimits L] :
    constantSheaf K (Type w) ⋙ L ≅ constantSheaf J (Type w) :=
  (((constantSheafΓAdj K (Type w)).comp adj).ofNatIsoRight
    (globalSectionsIsoOfAdjunction adj)).leftAdjointUniq (constantSheafΓAdj J (Type w))

/-- A left exact left adjoint between the topoi of sheaves of sets on two small sites carries
constant sheaves to constant sheaves. This is
`Stacks.ConstantSheaf.isConstant_obj` without its two final-object hypotheses. -/
public lemma isConstant_obj_of_smallSites (adj : L ⊣ R) [PreservesFiniteLimits L]
    (G : Sheaf K (Type w)) [Sheaf.IsConstant K G] : Sheaf.IsConstant J (L.obj G) := by
  obtain ⟨E, ⟨e⟩⟩ := Sheaf.mem_essImage_of_isConstant K G
  exact Sheaf.isConstant_of_iso J
    (L.mapIso e.symm ≪≫ (inverseImageConstantSheafIsoOfSmallSites adj).app E)

end Transfer

/-! ### Restriction to an object of the site -/

section Over

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C) (U : C)

/-- **Restriction to an object of the site carries a constant sheaf of sets to the constant
sheaf on the same set**, with no final object assumed in the site.

Restriction to `U` is restriction along `Over.forget U`, which is both continuous and
cocontinuous, so it is a left adjoint
(`CategoryTheory.Functor.sheafAdjunctionCocontinuous`); it is left exact because it is also the
right adjoint of `j_{U!}`. This is
`Stacks.ConstantSheaf.overPullbackConstantSheafIsoType` with its final-object hypothesis
removed, and it needs no binary products in `C` because the adjoint pair used is not
`Over.forget U ⊣ Over.star U`. -/
public def overPullbackConstantSheafIsoOfSmallSite :
    constantSheaf J (Type w) ⋙ J.overPullback (Type w) U ≅ constantSheaf (J.over U) (Type w) :=
  inverseImageConstantSheafIsoOfSmallSites
    ((Over.forget U).sheafAdjunctionCocontinuous (Type w) (J.over U) J)

/-- Restriction to an object of the site preserves constant sheaves of sets, with no final
object assumed in the site. -/
public lemma isConstant_overPullback_of_smallSite (F : Sheaf J (Type w))
    [Sheaf.IsConstant J F] :
    Sheaf.IsConstant (J.over U) ((J.overPullback (Type w) U).obj F) :=
  isConstant_obj_of_smallSites
    ((Over.forget U).sheafAdjunctionCocontinuous (Type w) (J.over U) J) F

end Over

end Stacks.ConstantSheaf

end
