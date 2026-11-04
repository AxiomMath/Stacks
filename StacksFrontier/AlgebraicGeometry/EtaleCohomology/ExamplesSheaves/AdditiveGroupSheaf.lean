module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Additive
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigZariskiStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteStructureSheaf
import StacksCore.Tactic.StacksAttribute

/-!
# The additive group sheaf on a site of schemes, and its cohomology

Let `S` be a scheme.  On any site of schemes over `S` the sheaf `Gₐ` of [Stacks, Tag 03P6] is
the abelian sheaf whose sections over `T/S` are the global functions `Γ(T, 𝒪_T)` under
addition.  Two descriptions of it are identified here, and they are the two halves of the
vocabulary [Stacks, Tag 03P6] speaks in.

* It is the structure sheaf `𝒪_S` of [Stacks, Tag 04HS] of that site with its values read as
  additive groups rather than as rings.  This is `Stacks.Sites.additiveGroupSheaf`, built from
  the ring-valued presheaf `Stacks.Sites.structurePresheaf` of the site, and it is what makes
  the notation `H^p_τ(X, 𝒪_X)` of the remark mean the same thing as `H^p_τ(X, Gₐ)`: the two
  are cohomology of one and the same abelian sheaf, not of two sheaves compared by a map.
* It is the functor of points of the additive group scheme `Gₐ,S` of [Stacks, Tag 022V],
  restricted to the site.  This is `Stacks.Sites.additiveGroupPresheafIsoPoints`, and it is
  what justifies the name: the group law on sections is addition of functions, transported
  from the group-scheme structure of the affine line.

The cohomology groups themselves are Mathlib's `Ext`-based `CategoryTheory.Sheaf.H`, and in
degree zero they are computed outright, for every one of the topologies at once
(`Stacks.Sites.sheafHZeroAddEquiv`): a site of schemes over `S` has `S` itself for a terminal
object, and degree-zero sheaf cohomology is sections over a terminal object.

## Main definitions

* `Stacks.Sites.additiveGroupPresheaf`: the presheaf `T ↦ (Γ(T, 𝒪_T), +)` on a site of
  schemes over `S`.
* `Stacks.Sites.additiveGroupSheaf`: the same presheaf as an abelian sheaf, once global
  functions are a sheaf of types on the site.
* `AlgebraicGeometry.BigFppfOver.additiveGroupSheaf`,
  `AlgebraicGeometry.BigEtaleOver.additiveGroupSheaf`,
  `AlgebraicGeometry.BigZariskiOver.additiveGroupSheaf`: `Gₐ` on the three sites
  `(Sch/S)_{fppf}`, `(Sch/S)_{étale}` and `(Sch/S)_{Zar}` whose cohomology the remark
  compares.

## Main results

* `Stacks.Sites.additiveGroupPresheafIsoPoints`: `Gₐ` is the functor of points of the additive
  group scheme over `S`.
* `Stacks.Sites.additiveGroupSheaf_obj`: the underlying presheaf of `Gₐ` is the structure
  presheaf of the site read additively, so `H^p_τ(X, Gₐ)` and `H^p_τ(X, 𝒪_X)` are cohomology
  of the same abelian sheaf.
* `Stacks.Sites.sheafHZeroAddEquiv`: `H^0_τ(S, Gₐ) = Γ(S, 𝒪_S)` on every site of schemes over
  `S` with a terminal object over the identity of `S`.  This is the degree-zero case of the
  chain of equalities of the remark, and it holds for every one of the topologies with no
  input from the theorem the remark specializes.  Its three instances are
  `AlgebraicGeometry.BigFppfOver.sheafHZeroAddEquiv`,
  `AlgebraicGeometry.BigEtaleOver.sheafHZeroAddEquiv` and
  `AlgebraicGeometry.BigZariskiOver.sheafHZeroAddEquiv`.
* `AlgebraicGeometry.additiveGroupSheafHZeroFppfEtaleAddEquiv` and
  `AlgebraicGeometry.additiveGroupSheafHZeroFppfZariskiAddEquiv`: the remark's chain of
  equalities in degree zero, `H^0_{fppf}(S, Gₐ) = H^0_{étale}(S, Gₐ) = H^0_{Zar}(S, Gₐ) =
  Γ(S, 𝒪_S)`.

## Implementation notes

**What is proved and what is not.**  The remark's chain of equalities

```
H^p_{fppf}(X, Gₐ) = H^p_{étale}(X, Gₐ) = H^p_{Zar}(X, Gₐ) = H^p(X, 𝒪_X)
```

is the specialization to `Gₐ` of [Stacks, Tag 03P2], and the equalities between two different
topologies in positive degree are exactly the content of that theorem — the acyclicity of the
Čech complex of a faithfully flat covering on a quasi-coherent module.  [Stacks, Tag 03P2] is
not in the tree, so those equalities are not available here and are not assumed either: no
declaration below takes any comparison of two cohomology groups as a hypothesis.  What is
delivered is the specialization data that the remark supplies on top of that theorem, namely
the identification of `Gₐ` on each of the three sites with the structure sheaf of
[Stacks, Tag 04HS] read additively, together with the degree-zero case of the chain, which
needs nothing from [Stacks, Tag 03P2].

**The group law.**  `AlgebraicGeometry.globalSectionsAdditive` is the additive group of global
functions written multiplicatively, which is the shape in which
`AlgebraicGeometry.additiveGroupBaseChangePointsIsoGlobalSections` identifies the points of
`Gₐ,S`.  `Stacks.Sites.additiveGroupPresheafIsoPoints` is therefore stated after the forgetful
retyping `AddCommGrpCat ⥤ AddGrpCat ⥤ GrpCat`, which is how that group law is recorded; it is
a whiskering of [Stacks, Tag 022V] along the functor to `Over S` and reproves nothing.

**Universes.**  `Stacks.Sites.structurePresheaf` fixes the shape of a site of schemes over `S`
at `C : Type (u + 1)` with `Category.{u} C`, which is the shape of every big and small site of
the chapter, and the coefficients then lie in `AddCommGrpCat.{u}`.  The `Ext` universe of
`CategoryTheory.Sheaf.H` is left free, and `HasSheafify` and `HasExt` are carried as instance
hypotheses rather than discharged: they are properties of the site, not of `Gₐ`.

## References

* [Stacks Project, Tag 03P6](https://stacks.math.columbia.edu/tag/03P6)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 04HS](https://stacks.math.columbia.edu/tag/04HS)
* [Stacks Project, Tag 022V](https://stacks.math.columbia.edu/tag/022V)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

universe w u

namespace Stacks.Sites

variable (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)

/-- **`Gₐ` on a site of schemes over `S`.**  The presheaf of additive groups whose sections
over an object `T/S` of the site are the global functions `Γ(T, 𝒪_T)`.  It is the structure
presheaf `Stacks.Sites.structurePresheaf` of the site with its ring-valued sections read as
additive groups. -/
@[sga "3 I 4.3.1"]
noncomputable abbrev additiveGroupPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  structurePresheaf S toOver ⋙ forget₂ RingCat AddCommGrpCat

/-- **Stacks 03P6, the identification of `Gₐ`.**  The additive group sheaf of a site of
schemes over `S` is the functor of points of the additive group scheme `Gₐ,S` of
[Stacks, Tag 022V], restricted to the site along `toOver`.

The comparison is stated after the forgetful retyping of `AddCommGrpCat` into `GrpCat`, which
is the shape in which `AlgebraicGeometry.additiveGroupBaseChangePointsIsoGlobalSections`
records that the group law on sections is addition of functions.  It is a whiskering of that
natural isomorphism and assumes nothing about the topology. -/
@[stacks 03P6 "Gₐ is the functor of points of the additive group scheme",
  sga "3 I 4.3.1" "more general"]
noncomputable def additiveGroupPresheafIsoPoints :
    toOver.op ⋙ yonedaGrpObj (Scheme.asOver (additiveGroupBaseChange S) S) ≅
      additiveGroupPresheaf S toOver ⋙ forget₂ AddCommGrpCat AddGrpCat ⋙ AddGrpCat.toGrp :=
  Functor.isoWhiskerLeft toOver.op (additiveGroupBaseChangePointsIsoGlobalSections S)

/-- The additive group presheaf of a site of schemes over `S` is a sheaf as soon as the
restriction to the site of the presheaf of types of global functions is a sheaf.  This is the
additive-group analogue of `Stacks.Sites.isSheaf_structurePresheaf`: amalgamating a compatible
family of functions element by element produces an additive map because the restriction maps
are jointly injective on a covering sieve. -/
theorem isSheaf_additiveGroupPresheaf (J : GrothendieckTopology C)
    (h : Presheaf.IsSheaf J (toOver.op ⋙ globalSectionsOver S)) :
    Presheaf.IsSheaf J (additiveGroupPresheaf S toOver) := by
  refine isSheaf_addCommGrpCat_of_isSheaf_forget J _ ?_
  rw [show additiveGroupPresheaf S toOver ⋙ CategoryTheory.forget AddCommGrpCat.{u} =
      toOver.op ⋙ globalSectionsOver S from structurePresheaf_comp_forget S toOver]
  exact (isSheaf_iff_isSheaf_of_type _ _).1 h

/-- **`Gₐ` as an abelian sheaf.**  The additive group sheaf of a site of schemes over `S` on
which global functions are a sheaf of types. -/
noncomputable def additiveGroupSheaf (J : GrothendieckTopology C)
    (h : Presheaf.IsSheaf J (toOver.op ⋙ globalSectionsOver S)) :
    Sheaf J AddCommGrpCat.{u} :=
  ⟨additiveGroupPresheaf S toOver, isSheaf_additiveGroupPresheaf S toOver J h⟩

/-- **Stacks 03P6, the notation `H^p_τ(X, 𝒪_X)`.**  The underlying presheaf of `Gₐ` is the
structure presheaf of the site read additively.  So the cohomology of `Gₐ` on a site of
schemes over `S` and the cohomology of the structure sheaf `𝒪_S` of [Stacks, Tag 04HS] on that
site are cohomology of one and the same abelian sheaf, which is what lets the two notations of
the remark be used interchangeably. -/
@[simp, stacks 03P6 "Gₐ is the structure sheaf of Stacks 04HS read additively"]
theorem additiveGroupSheaf_obj (J : GrothendieckTopology C)
    (h : Presheaf.IsSheaf J (toOver.op ⋙ globalSectionsOver S)) :
    (additiveGroupSheaf S toOver J h).obj =
      structurePresheaf S toOver ⋙ forget₂ RingCat AddCommGrpCat :=
  rfl

/-- The global functions of a scheme, read as an additive group.  This is the value of `Gₐ` at
a terminal object of a site of schemes over that scheme. -/
@[sga "3 I 4.3.1" "partial"]
noncomputable abbrev globalSectionsAddCommGrp : AddCommGrpCat.{u} :=
  (forget₂ RingCat AddCommGrpCat).obj
    ((forget₂ CommRingCat RingCat).obj (Scheme.Γ.obj (op S)))

/-- **Stacks 03P6 in degree zero.**  On a site of schemes over `S` with a terminal object `X₀`,
the degree-zero cohomology of `Gₐ` is the additive group of global functions on the scheme over
`S` that `X₀` names.  This is the degree-zero case of the remark's chain of equalities, and it
holds for every topology at once with no input from [Stacks, Tag 03P2]: degree-zero sheaf
cohomology is sections over a terminal object, and the sections of `Gₐ` are the global
functions. -/
@[stacks 03P6 "degree zero: H⁰ of Gₐ is the additive group of global functions"]
noncomputable def sheafHZeroAddEquiv (J : GrothendieckTopology C)
    (h : Presheaf.IsSheaf J (toOver.op ⋙ globalSectionsOver S))
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
    {X₀ : C} (hX₀ : IsTerminal X₀) :
    Sheaf.H (additiveGroupSheaf S toOver J h) 0 ≃+
      (additiveGroupPresheaf S toOver).obj (op X₀) :=
  Sheaf.H.equiv₀ _ hX₀

end Stacks.Sites

namespace AlgebraicGeometry

variable (S : Scheme.{u})

/-! ### `Gₐ` on the three sites of the remark -/

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (hS : B.Contains S)

/-- **Stacks 03P6, the big fppf site.**  `Gₐ` as an abelian sheaf on `(Sch/S)_{fppf}`.  Its
underlying presheaf is the structure sheaf of [Stacks, Tag 04HS] of that site read additively,
so its cohomology is the group the remark also writes `H^p_{fppf}(X, 𝒪_X)`. -/
@[stacks 03P6 "Gₐ on the big fppf site"]
noncomputable def additiveGroupSheaf : Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  Stacks.Sites.additiveGroupSheaf S (Over.post (X := B.obj hS) B.inclusion) (topology B S hS)
    (isSheaf_bigFppf_of_isSheaf_fpqc B S hS _
      (Stacks.Sites.isSheaf_fpqcOver_globalSections S))

/-- The underlying presheaf of `Gₐ` on the big fppf site over `S` is the presheaf of global
functions read additively. -/
@[simp]
theorem additiveGroupSheaf_obj :
    (additiveGroupSheaf S B hS).obj =
      Stacks.Sites.structurePresheaf S (Over.post (X := B.obj hS) B.inclusion) ⋙
        forget₂ RingCat AddCommGrpCat :=
  rfl

/-- **Stacks 03P6 in degree zero, fppf.**  `H^0_{fppf}(S, Gₐ) = Γ(S, 𝒪_S)`: the big fppf site
over `S` has `S` itself for a terminal object, and degree-zero sheaf cohomology is sections
over a terminal object. -/
@[stacks 03P6 "degree zero on the big fppf site"]
noncomputable def sheafHZeroAddEquiv [HasSheafify (topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (topology B S hS) AddCommGrpCat.{u})] :
    Sheaf.H (additiveGroupSheaf S B hS) 0 ≃+ Stacks.Sites.globalSectionsAddCommGrp S :=
  Stacks.Sites.sheafHZeroAddEquiv S _ _ _ Over.mkIdTerminal

end BigFppfOver

namespace BigEtaleOver

variable (B : BigEtaleSite.{u}) (hS : B.Contains S)

/-- **Stacks 03P6, the big étale site.**  `Gₐ` as an abelian sheaf on `(Sch/S)_{étale}`.  Its
underlying presheaf is the structure sheaf of [Stacks, Tag 04HS] of that site read additively,
so its cohomology is the group the remark also writes `H^p_{étale}(X, 𝒪_X)`. -/
@[stacks 03P6 "Gₐ on the big étale site"]
noncomputable def additiveGroupSheaf : Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  Stacks.Sites.additiveGroupSheaf S (Over.post (X := B.obj S hS) B.inclusion)
    (topology B S hS)
    (isSheaf_chosenBigEtale_of_isSheaf_fpqc B S hS _
      (Stacks.Sites.isSheaf_fpqcOver_globalSections S))

/-- The underlying presheaf of `Gₐ` on the big étale site over `S` is the presheaf of global
functions read additively. -/
@[simp]
theorem additiveGroupSheaf_obj :
    (additiveGroupSheaf S B hS).obj =
      Stacks.Sites.structurePresheaf S (Over.post (X := B.obj S hS) B.inclusion) ⋙
        forget₂ RingCat AddCommGrpCat :=
  rfl

/-- **Stacks 03P6 in degree zero, étale.**  `H^0_{étale}(S, Gₐ) = Γ(S, 𝒪_S)`: the big étale
site over `S` has `S` itself for a terminal object, and degree-zero sheaf cohomology is
sections over a terminal object. -/
@[stacks 03P6 "degree zero on the big étale site"]
noncomputable def sheafHZeroAddEquiv [HasSheafify (topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (topology B S hS) AddCommGrpCat.{u})] :
    Sheaf.H (additiveGroupSheaf S B hS) 0 ≃+ Stacks.Sites.globalSectionsAddCommGrp S :=
  Stacks.Sites.sheafHZeroAddEquiv S _ _ _ Over.mkIdTerminal

end BigEtaleOver

namespace BigZariskiOver

variable (B : BigZariskiSite.{u}) (hS : B.Contains S)

/-- **Stacks 03P6, the big Zariski site.**  `Gₐ` as an abelian sheaf on `(Sch/S)_{Zar}`.  Its
underlying presheaf is the structure sheaf of [Stacks, Tag 04HS] of that site read additively,
so its cohomology is the group the remark also writes `H^p_{Zar}(X, 𝒪_X)`. -/
@[stacks 03P6 "Gₐ on the big Zariski site"]
noncomputable def additiveGroupSheaf : Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  Stacks.Sites.additiveGroupSheaf S (Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion)
    (topology B S hS)
    (isSheaf_bigZariski_of_isSheaf_fpqc B S hS _
      (Stacks.Sites.isSheaf_fpqcOver_globalSections S))

/-- The underlying presheaf of `Gₐ` on the big Zariski site over `S` is the presheaf of global
functions read additively. -/
@[simp]
theorem additiveGroupSheaf_obj :
    (additiveGroupSheaf S B hS).obj =
      Stacks.Sites.structurePresheaf S
          (Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion) ⋙
        forget₂ RingCat AddCommGrpCat :=
  rfl

/-- **Stacks 03P6 in degree zero, Zariski.**  `H^0_{Zar}(S, Gₐ) = Γ(S, 𝒪_S)`: the big Zariski
site over `S` has `S` itself for a terminal object, and degree-zero sheaf cohomology is
sections over a terminal object. -/
@[stacks 03P6 "degree zero on the big Zariski site"]
noncomputable def sheafHZeroAddEquiv [HasSheafify (topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (topology B S hS) AddCommGrpCat.{u})] :
    Sheaf.H (additiveGroupSheaf S B hS) 0 ≃+ Stacks.Sites.globalSectionsAddCommGrp S :=
  Stacks.Sites.sheafHZeroAddEquiv S _ _ _ Over.mkIdTerminal

end BigZariskiOver

/-! ### The chain of equalities in degree zero -/

section Chain

variable (Bf : BigFppfSite.{u}) (hSf : Bf.Contains S)
  (Be : BigEtaleSite.{u}) (hSe : Be.Contains S)
  (Bz : BigZariskiSite.{u}) (hSz : Bz.Contains S)
  [HasSheafify (BigFppfOver.topology Bf S hSf) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (BigFppfOver.topology Bf S hSf) AddCommGrpCat.{u})]
  [HasSheafify (BigEtaleOver.topology Be S hSe) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (BigEtaleOver.topology Be S hSe) AddCommGrpCat.{u})]
  [HasSheafify (BigZariskiOver.topology Bz S hSz) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (BigZariskiOver.topology Bz S hSz) AddCommGrpCat.{u})]

/-- **Stacks 03P6 in degree zero, fppf against étale.**  `H^0_{fppf}(S, Gₐ) =
H^0_{étale}(S, Gₐ)`: both are the additive group `Γ(S, 𝒪_S)` of global functions.  This is one
leg of the remark's chain of equalities, in the degree in which it needs nothing from
[Stacks, Tag 03P2]. -/
@[stacks 03P6 "degree zero: fppf against étale"]
noncomputable def additiveGroupSheafHZeroFppfEtaleAddEquiv :
    Sheaf.H (BigFppfOver.additiveGroupSheaf S Bf hSf) 0 ≃+
      Sheaf.H (BigEtaleOver.additiveGroupSheaf S Be hSe) 0 :=
  (BigFppfOver.sheafHZeroAddEquiv S Bf hSf).trans
    (BigEtaleOver.sheafHZeroAddEquiv S Be hSe).symm

/-- **Stacks 03P6 in degree zero, fppf against Zariski.**  `H^0_{fppf}(S, Gₐ) =
H^0_{Zar}(S, Gₐ)`: both are the additive group `Γ(S, 𝒪_S)` of global functions.  Together with
`AlgebraicGeometry.additiveGroupSheafHZeroFppfEtaleAddEquiv` this is the remark's whole chain
of equalities in degree zero, the rightmost term `H^0(S, 𝒪_S)` being `Γ(S, 𝒪_S)` as well. -/
@[stacks 03P6 "degree zero: fppf against Zariski"]
noncomputable def additiveGroupSheafHZeroFppfZariskiAddEquiv :
    Sheaf.H (BigFppfOver.additiveGroupSheaf S Bf hSf) 0 ≃+
      Sheaf.H (BigZariskiOver.additiveGroupSheaf S Bz hSz) 0 :=
  (BigFppfOver.sheafHZeroAddEquiv S Bf hSf).trans
    (BigZariskiOver.sheafHZeroAddEquiv S Bz hSz).symm

end Chain

end AlgebraicGeometry

end
