module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomSections
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfStructureSheaf

/-!
# The internal hom on the big fppf site of a scheme (Stacks 03EM)

Stacks 03EM says that for a site `C` with a sheaf of rings `𝒪`, a presheaf of `𝒪`-modules `F`
and a *sheaf* of `𝒪`-modules `G`, the internal hom `𝓗om_𝒪(F, G)` is a sheaf of `𝒪`-modules.
This file is that statement at the big fppf site `(Sch/S)_fppf` of a scheme, with `𝒪` its
structure sheaf of Stacks 03DU.

Two things have to be supplied, and both are cheap.  The general statement wants a presheaf of
*commutative* rings, while `AlgebraicGeometry.BigFppfOver.structureSheaf` is a sheaf of
(possibly noncommutative) rings; `commStructurePresheaf` is the commutative lift, global
functions `T ↦ Γ(T, 𝒪_T)` read in `CommRingCat`, and `oforget_commStructurePresheaf` says that
forgetting commutativity returns the structure sheaf *on the nose*.  No sheafification,
smallness or `UnivLE` hypothesis is needed: the general theorem asks only that the target be a
sheaf.

**The module universe rises by one, and this is not an artifact.**  A section of the internal
hom over `T` is a morphism of presheaves of modules on the slice site `(Sch/S)_fppf / T`, whose
objects form a `Type (u + 1)`; so the internal hom of two `u`-small modules on the big fppf site
is a module at universe `u + 1`.  `sheafHom` therefore takes two objects of
`SheafOfModules.{u}` and returns an object of `SheafOfModules.{u + 1}`.  The gluing statements
below are unaffected by this, because they only ever glue *sections*.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.commStructurePresheaf`: the structure sheaf of the big fppf
  site over `S`, valued in commutative rings.
* `AlgebraicGeometry.BigFppfOver.homPresheaf` and
  `AlgebraicGeometry.BigFppfOver.sheafHom`: the internal hom `𝓗om_𝒪(F, G)` on the big fppf site
  over `S`, as a presheaf of modules and as a sheaf of modules.

## Main results

* `AlgebraicGeometry.BigFppfOver.homPresheaf_isSheaf`: **Stacks 03EM at the big fppf site of a
  scheme.**  The internal hom is a sheaf as soon as the target is.
* `AlgebraicGeometry.BigFppfOver.bijective_restrictToCover`: the equalizer form (Stacks 04TQ) at
  the big fppf site — morphisms `F|_T ⟶ G|_T` are exactly the compatible families of morphisms
  on the members of a covering sieve of `T`.
* `AlgebraicGeometry.BigFppfOver.existsUnique_hom_of_isCompatible` and
  `AlgebraicGeometry.BigFppfOver.exists_iso_of_isCompatible`: the form the gluing step of
  Stacks 03DX (1) consumes — a compatible family of local morphisms, resp. isomorphisms, on a
  family of objects covering the final object of `(Sch/S)_fppf` glues to a unique global
  morphism, resp. to an isomorphism.

## Implementation notes

Nothing here carries a `stacks` attribute.  Tag 03EM is already attributed at its general-site
statement `internalHom_isSheaf`, and whether the big-site instance belongs to its covering set is
not decided here.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04TQ](https://stacks.math.columbia.edu/tag/04TQ)
* [Stacks Project, Tag 04TT](https://stacks.math.columbia.edu/tag/04TT)
-/

@[expose] public section

open CategoryTheory Opposite

universe u w

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The structure sheaf of the big fppf site over `S`, valued in commutative rings.**  An
object `T` is sent to the ring `Γ(T, 𝒪_T)` of global functions on its underlying scheme.  This
is the presheaf `Stacks.Sites.structurePresheaf S (Over.post B.inclusion)` of
`AlgebraicGeometry.BigFppfOver.structureSheaf` before commutativity is forgotten. -/
public noncomputable abbrev commStructurePresheaf : (BigFppfOver B S hS)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Over.post B.inclusion ⋙ Over.forget S).op ⋙ Scheme.Γ

/-- Forgetting commutativity returns the structure sheaf of the big fppf site over `S` on the
nose, so a module over the one is a module over the other with no comparison map. -/
public theorem oforget_commStructurePresheaf :
    Oforget (commStructurePresheaf B S hS) = (structureSheaf B S hS).obj := rfl

/-- **The internal hom `𝓗om_𝒪(F, G)` on the big fppf site over `S`** (Stacks 04TT): the presheaf
whose sections over `T` are the `𝒪|_T`-linear maps `F|_T ⟶ G|_T` on the localization at `T`.
Its module universe is `u + 1`, those linear maps being indexed by the objects of that
localization. -/
public noncomputable abbrev homPresheaf
    (F G : PresheafOfModules.{u} (structureSheaf B S hS).obj) :
    PresheafOfModules.{u + 1} (structureSheaf B S hS).obj :=
  internalHom (commStructurePresheaf B S hS) F G

/-- **Stacks 03EM at the big fppf site of a scheme.**  For a presheaf of modules `F` and a
*sheaf* of modules `G` on `(Sch/S)_fppf`, the internal hom `𝓗om_𝒪(F, G)` is a sheaf.

This is the general-site theorem `internalHom_isSheaf` with the site, the topology and the
structure sheaf supplied; by `oforget_commStructurePresheaf` the ring data match definitionally,
so no transport is involved.  As in the general statement, `𝒪` itself is not required to be a
sheaf of rings and `F` is not required to be a sheaf. -/
public theorem homPresheaf_isSheaf (F : PresheafOfModules.{u} (structureSheaf B S hS).obj)
    (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    Presheaf.IsSheaf (topology B S hS) (homPresheaf B S hS F G.val).presheaf :=
  internalHom_isSheaf (commStructurePresheaf B S hS) F G.val G.isSheaf

/-- **`SheafHom(F, G)` on the big fppf site over `S`**, as an object of `SheafOfModules`.  Its
module universe is one above that of `F` and `G`; see the module docstring. -/
public noncomputable def sheafHom (F G : SheafOfModules.{u} (structureSheaf B S hS)) :
    SheafOfModules.{u + 1} (structureSheaf B S hS) where
  val := homPresheaf B S hS F.val G.val
  isSheaf := homPresheaf_isSheaf B S hS F.val G

/-- **The equalizer form of Stacks 03EM at the big fppf site** (Stacks 04TQ, "maps of sheaves
glue").  For a covering sieve of an object `T` of `(Sch/S)_fppf`, restricting a morphism
`F|_T ⟶ G|_T` to the members of the sieve is a bijection onto the compatible families. -/
public theorem bijective_restrictToCover
    (F : PresheafOfModules.{u} (structureSheaf B S hS).obj)
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {U : BigFppfOver B S hS}
    (c : (topology B S hS).Cover U) :
    Function.Bijective (restrictToCover (commStructurePresheaf B S hS) F G.val c) :=
  internalHom_glue (commStructurePresheaf B S hS) F G.val c G.isSheaf

/-- Stacks 03EM at the big fppf site, read on the underlying presheaf of types of sections.
This is the form the gluing lemmas consume. -/
public theorem homPresheaf_isSheaf_forget
    (F : PresheafOfModules.{u} (structureSheaf B S hS).obj)
    (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    Presheaf.IsSheaf (topology B S hS)
      ((homPresheaf B S hS F G.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ _ (homPresheaf_isSheaf B S hS F G)

/-- **The one-element family at the final object covers the top.**  The final object of
`(Sch/S)_fppf` is `S` over itself, every object has a unique morphism to it, so the sieve of
objects it generates is the maximal sieve.  This exhibits the `CoversTop` hypothesis of the
gluing statements below as satisfiable. -/
public theorem coversTop_terminal :
    (topology B S hS).CoversTop (fun (_ : PUnit.{1}) => Over.mk (𝟙 (B.obj hS))) := by
  intro W
  convert (topology B S hS).top_mem W
  ext Z f
  simp only [Sieve.top_apply, iff_true]
  exact ⟨PUnit.unit, ⟨Over.mkIdTerminal.from Z⟩⟩

/-- **Morphisms into a sheaf of modules glue over a covering family of the final object of
`(Sch/S)_fppf`.**  Given objects `X i` covering the final object and morphisms
`α i : F|_{X i} ⟶ G|_{X i}` agreeing after relocalization to any common refinement, there is a
unique morphism `F ⟶ G` restricting to the `α i`.

This is the 03EM half of the gluing step of Stacks 03DX (1) for `τ = fppf`: it is what assembles
local morphisms on the members of a covering family of `(Sch/S)_fppf` into a global one. -/
public theorem existsUnique_hom_of_isCompatible
    (F : PresheafOfModules.{u} (structureSheaf B S hS).obj)
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    {I : Type w} {X : I → BigFppfOver B S hS} (hX : (topology B S hS).CoversTop X)
    {α : Presheaf.FamilyOfElementsOnObjects
      ((homPresheaf B S hS F G.val).presheaf ⋙ CategoryTheory.forget _) X}
    (hα : α.IsCompatible) :
    ∃! φ : F ⟶ G.val,
      ∀ i, (restrFun (commStructurePresheaf B S hS) (X i)).map φ = α i :=
  _root_.existsUnique_hom_of_isCompatible (commStructurePresheaf B S hS) F G.val hX
    (homPresheaf_isSheaf_forget B S hS F G) hα

/-- **Local isomorphisms glue to an isomorphism of sheaves of modules on `(Sch/S)_fppf`.**  This
is the sentence "the sheaf property of `SheafHom` assembles the local isomorphisms into a global
one" of the proof of Stacks 03DX (1), with the site, the topology and the structure sheaf
supplied.  Both `F` and `G` are sheaves here, which the application has: the source is an
associated module and the target is the given quasi-coherent module. -/
public theorem exists_iso_of_isCompatible (F G : SheafOfModules.{u} (structureSheaf B S hS))
    {I : Type w} {X : I → BigFppfOver B S hS} (hX : (topology B S hS).CoversTop X)
    (e : ∀ i, (restrFun (commStructurePresheaf B S hS) (X i)).obj F.val ≅
      (restrFun (commStructurePresheaf B S hS) (X i)).obj G.val)
    (he : Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (F := (homPresheaf B S hS F.val G.val).presheaf ⋙ CategoryTheory.forget _)
      (fun i => (e i).hom)) :
    ∃ φ : F ≅ G,
      ∀ i, (restrFun (commStructurePresheaf B S hS) (X i)).map φ.hom.val = (e i).hom := by
  obtain ⟨φ, hφ⟩ := _root_.exists_iso_of_isCompatible (commStructurePresheaf B S hS) F.val
    G.val hX F.isSheaf G.isSheaf e he
  exact ⟨(SheafOfModules.fullyFaithfulForget _).preimageIso φ, hφ⟩

end BigFppfOver

end AlgebraicGeometry

end
