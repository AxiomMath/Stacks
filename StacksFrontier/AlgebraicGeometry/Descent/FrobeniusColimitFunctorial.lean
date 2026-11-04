module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectEssSurj
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Functoriality of the Frobenius colimit of the structure sheaf

Let `p` be a prime. For a scheme `X` in characteristic `p` the sheaf of rings `colim_F 𝒪_X` of
Stacks Tag 0EXB is `AlgebraicGeometry.frobeniusColimitRingSheaf`, built in
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStructureSheaf` as the colimit of the
structure sheaf along the `p`-th power endomorphism. This file makes that construction
**functorial in the scheme**: a morphism `f : X ⟶ Y` of schemes in characteristic `p` induces a
canonical morphism of sheaves of rings

`colim_F 𝒪_Y ⟶ f_*(colim_F 𝒪_X)`

whose composition with the stage-`n` coprojection of `colim_F 𝒪_Y` is the comorphism of `f`
followed by the stage-`n` coprojection of `colim_F 𝒪_X`, and that assignment is *strictly*
compatible with identities and composition. Extension of scalars along it is then the transition
functor between the categories of finite locally free modules over the Frobenius colimits, which
are the fibre categories of the category fibred in groupoids of Stacks Tag 0EXE.

## Main definitions

* `CategoryTheory.Limits.endoSequenceCocone` and `CategoryTheory.Limits.endoColimitDesc`: a
  family `g : ℕ → (R ⟶ T)` with `φ ≫ g (n + 1) = g n` is a cocone on the diagram of iterates of
  an endomorphism `φ` of `R`, and the morphism `colim φ ⟶ T` it descends to.
* `AlgebraicGeometry.Scheme.Hom.ringSheafPushforward`: pushforward of sheaves of rings along a
  morphism of schemes, read on the sites of opens.
* `AlgebraicGeometry.Scheme.Hom.ringSheafOnOpensHom` and
  `AlgebraicGeometry.frobeniusRingSheafOnOpensHom`: the comorphism of a morphism of schemes and
  the `p`-th power endomorphism of the structure sheaf, read on the sites of opens.
* `AlgebraicGeometry.frobeniusColimitStructureSheafHom`: **the canonical morphism
  `colim_F 𝒪_Y ⟶ f_*(colim_F 𝒪_X)`.**
* `AlgebraicGeometry.frobeniusColimitVectorBundlesPullback`: **the transition functor** between
  the categories of finite locally free modules over the Frobenius colimits, namely extension of
  scalars along that morphism.
* `AlgebraicGeometry.frobeniusColimitPullbackId`,
  `AlgebraicGeometry.frobeniusColimitPullbackComp`,
  `AlgebraicGeometry.frobeniusColimitVectorBundlesPullbackId` and
  `AlgebraicGeometry.frobeniusColimitVectorBundlesPullbackComp`: the identity and composition
  comparisons of those transition functors, on all sheaves of modules and on the finite locally
  free ones.
* `AlgebraicGeometry.frobeniusColimitPullbackIdOfEq` and
  `AlgebraicGeometry.frobeniusColimitPullbackCompOfEq`: the same two comparisons with the
  morphisms of Frobenius-colimit sheaves as parameters and the equations identifying them with the
  identity, respectively with the composite, as hypotheses. The two comparisons above are the
  instances of these at the canonical morphisms.

## Main results

* `AlgebraicGeometry.ringSheafOnOpensHom_comp_frobenius`: **the comorphism of a morphism of
  schemes commutes with the `p`-th power endomorphisms of the two structure sheaves**, because a
  morphism of sheaves of rings commutes with `p`-th powers. This is the compatibility which makes
  the legs below a cocone.
* `AlgebraicGeometry.frobeniusColimitι_comp_frobeniusColimitStructureSheafHom`: **the stage
  formula.** The canonical morphism is determined by the requirement that it turn the stage-`n`
  coprojection of `colim_F 𝒪_Y` into the comorphism of `f` followed by the stage-`n` coprojection
  of `colim_F 𝒪_X`; uniqueness is `CategoryTheory.Limits.eq_endoColimitDesc`.
* `AlgebraicGeometry.frobeniusColimitStructureSheafHom_id` and
  `AlgebraicGeometry.frobeniusColimitStructureSheafHom_comp`: **the canonical morphisms are
  strictly functorial** — the identity of `X` induces the identity of `colim_F 𝒪_X`, and a
  composite induces the composite, on the nose and not merely up to isomorphism.
* `AlgebraicGeometry.isFiniteLocallyFree_frobeniusColimitPullback`: **extension of scalars along
  the canonical morphism preserves finite local freeness**, so it restricts to the fibre
  categories.
* `AlgebraicGeometry.frobeniusColimitPullbackCompOfEq_assoc`,
  `AlgebraicGeometry.frobeniusColimitPullbackIdOfEq_comp` and
  `AlgebraicGeometry.frobeniusColimitPullbackCompOfEq_id`: **the transition functors and their
  comparisons satisfy the three pseudofunctor coherences** — the associativity pentagon and the
  two unit conditions. These are the coherences a pseudofunctor out of the big h category over
  `S` into categories of Frobenius-colimit modules needs, and they are the content of the
  canonical morphism being strictly functorial: substituting the equations that present the
  composite morphisms leaves Mathlib's
  `CategoryTheory.SheafOfModules.pullback_assoc`, `pullback_id_comp` and `pullback_comp_id`.

## Implementation notes

**Why the colimit is formed on the site of opens.** The `HasColimit` instance for sheaves of
rings is stated for a category of the form `CategoryTheory.Sheaf J RingCat`, and instance
resolution does not unfold `TopCat.Sheaf`, which hides the site and its topology. The morphisms
entering the cocone are therefore spelled with `AlgebraicGeometry.Scheme.ringSheafOnOpens` and
`AlgebraicGeometry.frobeniusColimitRingSheaf`, the re-typings introduced in
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundles` for exactly this reason;
`AlgebraicGeometry.Scheme.Hom.ringSheafOnOpensHom` and
`AlgebraicGeometry.frobeniusRingSheafOnOpensHom` are the two further re-typings this file needs,
of the comorphism of a morphism of schemes and of the Frobenius endomorphism of the structure
sheaf.

**Why the cocone is built generically.** `CategoryTheory.Limits.endoSequence` is a
`CategoryTheory.Functor.ofSequence`, so the value of its `map` on a single step is equal to the
endomorphism but not definitionally so, and the rewrite which identifies them has to be performed
where the ambient category is a variable: performed in the category of sheaves of rings on the
opens of a scheme it produces a term whose `CategoryTheory.Quiver` instance is reached by a
different path from the one the surrounding morphisms carry, and every subsequent rewrite fails.
`CategoryTheory.Limits.endoSequenceCocone` therefore does that step once, for an arbitrary
category, and the Frobenius-specific compatibility
`AlgebraicGeometry.frobenius_comp_pushforward_frobeniusColimitι` is stated with no reference to
the diagram at all.

**Why the comparisons are stated with the morphisms as parameters.** The canonical morphism
`colim_F 𝒪_Z ⟶ (f ≫ g)_*(colim_F 𝒪_X)` is a morphism out of a sequential colimit, so it is
*characterized* by its composition law and not computed by it: the equation
`AlgebraicGeometry.frobeniusColimitStructureSheafHom_comp` is propositional, not definitional.
Mathlib's `CategoryTheory.SheafOfModules.pullbackComp` and the three coherences it satisfies
mention the composite `φ ≫ F_*ψ` on the nose, so each comparison here has to be transported along
that equation, and the transports sit between the whiskerings in the coherences, where no rewrite
reaches them. Stating the comparisons with the morphisms as parameters and the equations as
hypotheses is what lets a coherence proof substitute the equations first; after the substitution
the transports are the identity and the coherence is Mathlib's.

**Strictness.** The identity and composition laws hold on the nose, not up to isomorphism,
because both sides are morphisms out of a colimit and agree on every coprojection: the comorphism
of a morphism of schemes is itself strictly functorial, `pushforward` of sheaves of rings along a
composite is the composite of the pushforwards definitionally, and the colimit has no further
choice to make. This is what lets the comparison isomorphisms of the transition functors be
`CategoryTheory.Limits.SheafOfModules.pullbackId` and `pullbackComp` of Mathlib transported along
an equality of morphisms, rather than new coherence data.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Frobenius

universe v u

namespace CategoryTheory.Limits

variable {𝒞 : Type u} [Category.{v} 𝒞] {R T : 𝒞}

/-- A family of morphisms out of `R` which absorbs one copy of `φ` on passing from stage `n + 1`
to stage `n` is a cocone on the diagram of iterates of `φ`. -/
noncomputable def endoSequenceCocone (φ : R ⟶ R) (g : ℕ → (R ⟶ T))
    (hg : ∀ n, φ ≫ g (n + 1) = g n) : Cocone (endoSequence φ) where
  pt := T
  ι := NatTrans.ofSequence g (fun n => by
    simp only [endoSequence_map_succ, Functor.const_obj_map]
    exact (hg n).trans (Category.comp_id _).symm)

/-- The stage-`n` leg of that cocone is the `n`-th member of the family. -/
@[simp]
lemma endoSequenceCocone_ι_app (φ : R ⟶ R) (g : ℕ → (R ⟶ T))
    (hg : ∀ n, φ ≫ g (n + 1) = g n) (n : ℕ) :
    (endoSequenceCocone φ g hg).ι.app n = g n := rfl

variable (φ : R ⟶ R) [HasColimit (endoSequence φ)]

/-- The morphism out of `colim φ` which a family of morphisms out of `R` absorbing one copy of
`φ` at every stage descends to. -/
noncomputable def endoColimitDesc (g : ℕ → (R ⟶ T)) (hg : ∀ n, φ ≫ g (n + 1) = g n) :
    colimit (endoSequence φ) ⟶ T :=
  colimit.desc (endoSequence φ) (endoSequenceCocone φ g hg)

/-- The descent of a compatible family restricts, on the stage-`n` coprojection, to the `n`-th
member of the family. -/
@[simp]
lemma endoColimitι_comp_endoColimitDesc (g : ℕ → (R ⟶ T)) (hg : ∀ n, φ ≫ g (n + 1) = g n)
    (n : ℕ) : endoColimitι φ n ≫ endoColimitDesc φ g hg = g n :=
  colimit.ι_desc (endoSequenceCocone φ g hg) n

/-- Two morphisms out of `colim φ` which agree on every coprojection are equal. -/
lemma endoColimit_hom_ext {α β : colimit (endoSequence φ) ⟶ T}
    (h : ∀ n, endoColimitι φ n ≫ α = endoColimitι φ n ≫ β) : α = β :=
  colimit.hom_ext h

/-- **The descent of a compatible family is the only morphism out of `colim φ` restricting to
it.** -/
lemma eq_endoColimitDesc (g : ℕ → (R ⟶ T)) (hg : ∀ n, φ ≫ g (n + 1) = g n)
    (α : colimit (endoSequence φ) ⟶ T) (hα : ∀ n, endoColimitι φ n ≫ α = g n) :
    α = endoColimitDesc φ g hg :=
  endoColimit_hom_ext φ fun n => by
    rw [hα, endoColimitι_comp_endoColimitDesc]

end CategoryTheory.Limits

namespace AlgebraicGeometry

variable {X Y Z W : Scheme.{u}} (p : ℕ) [Fact p.Prime]

/-- Pushforward of sheaves of rings along a morphism of schemes, read on the sites of opens. -/
noncomputable abbrev Scheme.Hom.ringSheafPushforward (f : X ⟶ Y) :
    Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology (Y : TopCat)) RingCat.{u} :=
  (Opens.map f.base).sheafPushforwardContinuous RingCat.{u} _ _

/-- The comorphism of a morphism of schemes, read on the sites of opens. This is
`AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`; only its type is spelled differently, so that
instance resolution, which does not unfold `TopCat.Sheaf`, can see the sites and their
topologies. -/
noncomputable def Scheme.Hom.ringSheafOnOpensHom (f : X ⟶ Y) :
    Y.ringSheafOnOpens ⟶ (f.ringSheafPushforward).obj X.ringSheafOnOpens :=
  f.toRingCatSheafHom

/-- The Frobenius endomorphism of the structure sheaf, read on the site of opens. This is
`AlgebraicGeometry.frobeniusRingCatSheafHom`; only its type is spelled differently, for the same
reason as `AlgebraicGeometry.Scheme.Hom.ringSheafOnOpensHom`. -/
@[sga "3 VIIA 4.3.3"]
noncomputable def frobeniusRingSheafOnOpensHom (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) : X.ringSheafOnOpens ⟶ X.ringSheafOnOpens :=
  frobeniusRingCatSheafHom X p hX

/-- The stage-`n + 1` coprojection of `colim_F 𝒪_X` absorbs one copy of the Frobenius
endomorphism of `𝒪_X` and becomes the stage-`n` coprojection, read on the site of opens. -/
lemma frobeniusRingSheafOnOpensHom_comp_frobeniusColimitι
    (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p) (n : ℕ) :
    frobeniusRingSheafOnOpensHom X p hX ≫ frobeniusColimitι X p hX (n + 1) =
      frobeniusColimitι X p hX n :=
  frobenius_comp_frobeniusStructureSheafι X p hX n

/-- **The comorphism of a morphism of schemes commutes with the Frobenius endomorphisms of the
two structure sheaves.** On sections both composites send a section `g` to the `p`-th power of
its image under the comorphism: the comorphism is a morphism of sheaves of rings, and the
Frobenius endomorphism is the `p`-th power map. -/
lemma ringSheafOnOpensHom_comp_frobenius (f : X ⟶ Y) (hX : IsInCharacteristic X p)
    (hY : IsInCharacteristic Y p) :
    f.ringSheafOnOpensHom ≫ (f.ringSheafPushforward).map (frobeniusRingSheafOnOpensHom X p hX) =
      frobeniusRingSheafOnOpensHom Y p hY ≫ f.ringSheafOnOpensHom := by
  apply Sheaf.hom_ext
  ext U g
  have h₁ : (RingCat.Hom.hom ((f.ringSheafOnOpensHom ≫
        (f.ringSheafPushforward).map (frobeniusRingSheafOnOpensHom X p hX)).hom.app U)) g =
      ((RingCat.Hom.hom (f.ringSheafOnOpensHom.hom.app U)) g) ^ p :=
    frobeniusPresheafHom_app_apply X p hX _ _
  have e : (RingCat.Hom.hom ((frobeniusRingSheafOnOpensHom Y p hY).hom.app U)) g = g ^ p :=
    frobeniusPresheafHom_app_apply Y p hY U.unop g
  have h₂ : (RingCat.Hom.hom ((frobeniusRingSheafOnOpensHom Y p hY ≫
        f.ringSheafOnOpensHom).hom.app U)) g =
      ((RingCat.Hom.hom (f.ringSheafOnOpensHom.hom.app U)) g) ^ p := by
    show (RingCat.Hom.hom (f.ringSheafOnOpensHom.hom.app U))
        ((RingCat.Hom.hom ((frobeniusRingSheafOnOpensHom Y p hY).hom.app U)) g) = _
    rw [e, map_pow]
  exact h₁.trans h₂.symm

/-- The legs of the cocone defining the canonical morphism of Frobenius colimits absorb one copy
of the Frobenius endomorphism of `𝒪_Y` on passing from stage `n + 1` to stage `n`. -/
lemma frobenius_comp_pushforward_frobeniusColimitι (f : X ⟶ Y) (hX : IsInCharacteristic X p)
    (hY : IsInCharacteristic Y p) (n : ℕ) :
    frobeniusRingSheafOnOpensHom Y p hY ≫ (f.ringSheafOnOpensHom ≫
        (f.ringSheafPushforward).map (frobeniusColimitι X p hX (n + 1))) =
      f.ringSheafOnOpensHom ≫ (f.ringSheafPushforward).map (frobeniusColimitι X p hX n) := by
  rw [← Category.assoc, ← ringSheafOnOpensHom_comp_frobenius p f hX hY, Category.assoc,
    ← Functor.map_comp, frobeniusRingSheafOnOpensHom_comp_frobeniusColimitι]

/-- **The canonical morphism `colim_F 𝒪_Y ⟶ f_*(colim_F 𝒪_X)`** induced by a morphism
`f : X ⟶ Y` of schemes in characteristic `p`. It is the descent of the cocone whose stage-`n` leg
is the comorphism of `f` followed by the stage-`n` coprojection of `colim_F 𝒪_X`. -/
noncomputable def frobeniusColimitStructureSheafHom (f : X ⟶ Y) (hX : IsInCharacteristic X p)
    (hY : IsInCharacteristic Y p) :
    frobeniusColimitRingSheaf Y p hY ⟶
      (f.ringSheafPushforward).obj (frobeniusColimitRingSheaf X p hX) :=
  endoColimitDesc (frobeniusRingSheafOnOpensHom Y p hY)
    (fun n => f.ringSheafOnOpensHom ≫
      (f.ringSheafPushforward).map (frobeniusColimitι X p hX n))
    (frobenius_comp_pushforward_frobeniusColimitι p f hX hY)

/-- **The stage formula for the canonical morphism of Frobenius colimits.** Composing the
stage-`n` coprojection of `colim_F 𝒪_Y` with it gives the comorphism of `f` followed by the
stage-`n` coprojection of `colim_F 𝒪_X`. By `CategoryTheory.Limits.eq_endoColimitDesc` this
determines it. -/
lemma frobeniusColimitι_comp_frobeniusColimitStructureSheafHom (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (n : ℕ) :
    frobeniusColimitι Y p hY n ≫ frobeniusColimitStructureSheafHom p f hX hY =
      f.ringSheafOnOpensHom ≫
        (f.ringSheafPushforward).map (frobeniusColimitι X p hX n) :=
  endoColimitι_comp_endoColimitDesc _ _ _ n

/-- The comorphism of the identity of a scheme is the identity of its structure sheaf. -/
lemma ringSheafOnOpensHom_id (X : Scheme.{u}) :
    Scheme.Hom.ringSheafOnOpensHom (𝟙 X) = 𝟙 X.ringSheafOnOpens := rfl

/-- The comorphism of a composite is the comorphism of the second factor followed by the
pushforward of the comorphism of the first. -/
lemma ringSheafOnOpensHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).ringSheafOnOpensHom =
      g.ringSheafOnOpensHom ≫ (g.ringSheafPushforward).map f.ringSheafOnOpensHom := rfl

/-- **The canonical morphism induced by an identity is an identity.** -/
lemma frobeniusColimitStructureSheafHom_id (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) :
    frobeniusColimitStructureSheafHom p (𝟙 X) hX hX = 𝟙 _ :=
  (eq_endoColimitDesc _ _ _ (𝟙 _) (fun n => by
    show frobeniusColimitι X p hX n ≫ 𝟙 _ = 𝟙 _ ≫ frobeniusColimitι X p hX n
    rw [Category.comp_id, Category.id_comp])).symm

/-- **The canonical morphisms compose strictly.** The morphism of Frobenius colimits induced by
`f ≫ g` is the one induced by `g` followed by the pushforward along `g` of the one induced by
`f`. -/
lemma frobeniusColimitStructureSheafHom_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (hZ : IsInCharacteristic Z p) :
    frobeniusColimitStructureSheafHom p (f ≫ g) hX hZ =
      frobeniusColimitStructureSheafHom p g hY hZ ≫
        (g.ringSheafPushforward).map (frobeniusColimitStructureSheafHom p f hX hY) :=
  (eq_endoColimitDesc _ _ _ _ (fun n => by
    show frobeniusColimitι Z p hZ n ≫ (frobeniusColimitStructureSheafHom p g hY hZ ≫
        (g.ringSheafPushforward).map (frobeniusColimitStructureSheafHom p f hX hY)) =
      Scheme.Hom.ringSheafOnOpensHom (f ≫ g) ≫
        ((f ≫ g).ringSheafPushforward).map (frobeniusColimitι X p hX n)
    rw [← Category.assoc, frobeniusColimitι_comp_frobeniusColimitStructureSheafHom,
      Category.assoc, ← Functor.map_comp,
      frobeniusColimitι_comp_frobeniusColimitStructureSheafHom,
      Functor.map_comp, ← Category.assoc]
    rfl)).symm

/-! ### transition functors -/

/-- **Extension of scalars along the canonical morphism of Frobenius colimits preserves finite
local freeness**, by `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback` for the
underlying continuous map of `f`. -/
theorem isFiniteLocallyFree_frobeniusColimitPullback (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (M : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf Y p hY))
    (h : SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((_root_.SheafOfModules.pullback
        (frobeniusColimitStructureSheafHom p f hX hY)).obj M) :=
  SheafOfModules.IsFiniteLocallyFree.pullback f.base _ M h

/-- **The transition functor of Stacks Tag 0EXE**: extension of scalars along the canonical
morphism of Frobenius colimits, from the finite locally free `colim_F 𝒪_Y`-modules to the finite
locally free `colim_F 𝒪_X`-modules. -/
noncomputable def frobeniusColimitVectorBundlesPullback (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) :
    frobeniusColimitVectorBundles Y p hY ⥤ frobeniusColimitVectorBundles X p hX :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ _root_.SheafOfModules.pullback.{u}
      (frobeniusColimitStructureSheafHom p f hX hY))
    (fun M => isFiniteLocallyFree_frobeniusColimitPullback p f hX hY M.1 M.2)

/-- Extension of scalars along a morphism **equal to** the identity of `colim_F 𝒪_X` is the
identity functor. The morphism is a parameter and the equation is a hypothesis, so that a proof
about this isomorphism may substitute the equation and be left with Mathlib's
`CategoryTheory.SheafOfModules.pullbackId`; `AlgebraicGeometry.frobeniusColimitPullbackId` is the
instance of it at the canonical morphism induced by `𝟙 X`. -/
noncomputable def frobeniusColimitPullbackIdOfEq (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p)
    (d : frobeniusColimitRingSheaf X p hX ⟶
      ((𝟙 X : X ⟶ X).ringSheafPushforward).obj (frobeniusColimitRingSheaf X p hX))
    (hd : d = 𝟙 (frobeniusColimitRingSheaf X p hX)) :
    _root_.SheafOfModules.pullback.{u} d ≅
      𝟭 (_root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)) :=
  eqToIso (congrArg (fun φ => _root_.SheafOfModules.pullback.{u} φ) hd) ≪≫
    _root_.SheafOfModules.pullbackId.{u} (frobeniusColimitRingSheaf X p hX)

/-- Extension of scalars along the canonical morphism induced by the identity of `X` is the
identity functor, on all sheaves of modules over `colim_F 𝒪_X`. -/
noncomputable def frobeniusColimitPullbackId (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) :
    _root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p (𝟙 X) hX hX) ≅
      𝟭 (_root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)) :=
  frobeniusColimitPullbackIdOfEq X p hX _ (frobeniusColimitStructureSheafHom_id X p hX)

/-- Extension of scalars along two morphisms of Frobenius-colimit sheaves is extension of
scalars along a morphism **equal to** their composite `a ≫ g_*b`. All three morphisms are
parameters and the equation is a hypothesis, so that a proof about this isomorphism may
substitute the equation and be left with Mathlib's
`CategoryTheory.SheafOfModules.pullbackComp`;
`AlgebraicGeometry.frobeniusColimitPullbackComp` is the instance of it at the canonical
morphisms. -/
noncomputable def frobeniusColimitPullbackCompOfEq (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (hZ : IsInCharacteristic Z p)
    (a : frobeniusColimitRingSheaf Z p hZ ⟶
      (g.ringSheafPushforward).obj (frobeniusColimitRingSheaf Y p hY))
    (b : frobeniusColimitRingSheaf Y p hY ⟶
      (f.ringSheafPushforward).obj (frobeniusColimitRingSheaf X p hX))
    (c : frobeniusColimitRingSheaf Z p hZ ⟶
      ((f ≫ g).ringSheafPushforward).obj (frobeniusColimitRingSheaf X p hX))
    (hc : c = a ≫ (g.ringSheafPushforward).map b) :
    _root_.SheafOfModules.pullback.{u} a ⋙ _root_.SheafOfModules.pullback.{u} b ≅
      _root_.SheafOfModules.pullback.{u} c :=
  _root_.SheafOfModules.pullbackComp.{u} a b ≪≫
    eqToIso (congrArg (fun φ => _root_.SheafOfModules.pullback.{u} φ) hc.symm)

/-- At the composite itself, `AlgebraicGeometry.frobeniusColimitPullbackCompOfEq` is Mathlib's
`CategoryTheory.SheafOfModules.pullbackComp`. -/
lemma frobeniusColimitPullbackCompOfEq_self (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (hZ : IsInCharacteristic Z p)
    (a : frobeniusColimitRingSheaf Z p hZ ⟶
      (g.ringSheafPushforward).obj (frobeniusColimitRingSheaf Y p hY))
    (b : frobeniusColimitRingSheaf Y p hY ⟶
      (f.ringSheafPushforward).obj (frobeniusColimitRingSheaf X p hX)) :
    frobeniusColimitPullbackCompOfEq p f g hX hY hZ a b _ rfl =
      _root_.SheafOfModules.pullbackComp.{u} a b := by
  simp only [frobeniusColimitPullbackCompOfEq]
  exact Iso.trans_refl _

/-- At the identity itself, `AlgebraicGeometry.frobeniusColimitPullbackIdOfEq` is Mathlib's
`CategoryTheory.SheafOfModules.pullbackId`. -/
lemma frobeniusColimitPullbackIdOfEq_self (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) :
    frobeniusColimitPullbackIdOfEq X p hX (𝟙 (frobeniusColimitRingSheaf X p hX)) rfl =
      _root_.SheafOfModules.pullbackId.{u} (frobeniusColimitRingSheaf X p hX) := by
  simp only [frobeniusColimitPullbackIdOfEq]
  exact Iso.refl_trans _

/-- Extension of scalars along the canonical morphisms induced by `g` and then by `f` is
extension of scalars along the one induced by `f ≫ g`, on all sheaves of modules. -/
noncomputable def frobeniusColimitPullbackComp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (hZ : IsInCharacteristic Z p) :
    _root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p g hY hZ) ⋙
        _root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p f hX hY) ≅
      _root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p (f ≫ g) hX hZ) :=
  frobeniusColimitPullbackCompOfEq p f g hX hY hZ _ _ _
    (frobeniusColimitStructureSheafHom_comp p f g hX hY hZ)

/-! ### The three pseudofunctor coherences of the transition functors -/

/-- **The associativity pentagon at the canonical composites.** The special case of
`AlgebraicGeometry.frobeniusColimitPullbackCompOfEq_assoc` in which every composite morphism is
literally the composite, so that each comparison is Mathlib's
`CategoryTheory.SheafOfModules.pullbackComp` and the pentagon is Mathlib's
`CategoryTheory.SheafOfModules.pullback_assoc`. -/
lemma frobeniusColimitPullbackCompOfEq_assoc_rfl (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (hZ : IsInCharacteristic Z p) (hW : IsInCharacteristic W p)
    (a : frobeniusColimitRingSheaf W p hW ⟶
      (h.ringSheafPushforward).obj (frobeniusColimitRingSheaf Z p hZ))
    (b : frobeniusColimitRingSheaf Z p hZ ⟶
      (g.ringSheafPushforward).obj (frobeniusColimitRingSheaf Y p hY))
    (c : frobeniusColimitRingSheaf Y p hY ⟶
      (f.ringSheafPushforward).obj (frobeniusColimitRingSheaf X p hX)) :
    Functor.isoWhiskerLeft (_root_.SheafOfModules.pullback.{u} a)
          (frobeniusColimitPullbackCompOfEq p f g hX hY hZ b c _ rfl) ≪≫
        frobeniusColimitPullbackCompOfEq p (f ≫ g) h hX hZ hW a
          (b ≫ (g.ringSheafPushforward).map c) _ rfl =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (frobeniusColimitPullbackCompOfEq p g h hY hZ hW a b _ rfl)
            (_root_.SheafOfModules.pullback.{u} c) ≪≫
          frobeniusColimitPullbackCompOfEq p f (g ≫ h) hX hY hW
            (a ≫ (h.ringSheafPushforward).map b) c _ rfl := by
  simp only [frobeniusColimitPullbackCompOfEq_self]
  exact _root_.SheafOfModules.pullback_assoc.{u} a b c

/-- **The associativity pentagon.** For three composable morphisms of schemes in characteristic
`p` and a choice of morphism of Frobenius-colimit sheaves for each of the four arrows obtained by
composing them, presented by the equations the comparison isomorphisms are built from, the two
routes from `pullback a ⋙ pullback b ⋙ pullback c` to `pullback d` agree.

Substituting the three equations that *define* the composite morphisms leaves Mathlib's
`CategoryTheory.SheafOfModules.pullback_assoc`; the fourth equation then holds definitionally,
pushforward of sheaves of rings along a morphism of schemes being strictly functorial. -/
lemma frobeniusColimitPullbackCompOfEq_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (hZ : IsInCharacteristic Z p) (hW : IsInCharacteristic W p)
    (a : frobeniusColimitRingSheaf W p hW ⟶
      (h.ringSheafPushforward).obj (frobeniusColimitRingSheaf Z p hZ))
    (b : frobeniusColimitRingSheaf Z p hZ ⟶
      (g.ringSheafPushforward).obj (frobeniusColimitRingSheaf Y p hY))
    (c : frobeniusColimitRingSheaf Y p hY ⟶
      (f.ringSheafPushforward).obj (frobeniusColimitRingSheaf X p hX))
    (ab : frobeniusColimitRingSheaf W p hW ⟶
      ((g ≫ h).ringSheafPushforward).obj (frobeniusColimitRingSheaf Y p hY))
    (hab : ab = a ≫ (h.ringSheafPushforward).map b)
    (bc : frobeniusColimitRingSheaf Z p hZ ⟶
      ((f ≫ g).ringSheafPushforward).obj (frobeniusColimitRingSheaf X p hX))
    (hbc : bc = b ≫ (g.ringSheafPushforward).map c)
    (d : frobeniusColimitRingSheaf W p hW ⟶
      ((f ≫ g ≫ h).ringSheafPushforward).obj (frobeniusColimitRingSheaf X p hX))
    (hd : d = a ≫ (h.ringSheafPushforward).map bc)
    (hd' : d = ab ≫ ((g ≫ h).ringSheafPushforward).map c) :
    Functor.isoWhiskerLeft (_root_.SheafOfModules.pullback.{u} a)
          (frobeniusColimitPullbackCompOfEq p f g hX hY hZ b c bc hbc) ≪≫
        frobeniusColimitPullbackCompOfEq p (f ≫ g) h hX hZ hW a bc d hd =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (frobeniusColimitPullbackCompOfEq p g h hY hZ hW a b ab hab)
            (_root_.SheafOfModules.pullback.{u} c) ≪≫
          frobeniusColimitPullbackCompOfEq p f (g ≫ h) hX hY hW ab c d hd' := by
  subst hab
  subst hbc
  subst hd
  exact frobeniusColimitPullbackCompOfEq_assoc_rfl p f g h hX hY hZ hW a b c

/-- **The left unit coherence.** For `e` equal to the identity of `colim_F 𝒪_Y`, the comparison
of the transition functors of `f` and of `𝟙 Y` is the identity comparison of `𝟙 Y` whiskered into
the transition functor of `f`.

Both the morphism `c` attached to the composite `f ≫ 𝟙 Y` and the identification of extension of
scalars along it with extension of scalars along `b` are parameters: the composite is `f` on the
nose, so the two agree, but a consumer that would have to *check* that — a pseudofunctor whose
arrow map is built from a sequential colimit — cannot afford to. -/
lemma frobeniusColimitPullbackIdOfEq_comp (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (e : frobeniusColimitRingSheaf Y p hY ⟶
      ((𝟙 Y : Y ⟶ Y).ringSheafPushforward).obj (frobeniusColimitRingSheaf Y p hY))
    (he : e = 𝟙 (frobeniusColimitRingSheaf Y p hY))
    (b : frobeniusColimitRingSheaf Y p hY ⟶
      (f.ringSheafPushforward).obj (frobeniusColimitRingSheaf X p hX))
    (c : frobeniusColimitRingSheaf Y p hY ⟶
      ((f ≫ 𝟙 Y).ringSheafPushforward).obj (frobeniusColimitRingSheaf X p hX))
    (hc : c = e ≫ ((𝟙 Y : Y ⟶ Y).ringSheafPushforward).map b)
    (hFE : _root_.SheafOfModules.pullback.{u} c = _root_.SheafOfModules.pullback.{u} b) :
    frobeniusColimitPullbackCompOfEq p f (𝟙 Y) hX hY hY e b c hc ≪≫ eqToIso hFE =
      Functor.isoWhiskerRight (frobeniusColimitPullbackIdOfEq Y p hY e he)
          (_root_.SheafOfModules.pullback.{u} b) ≪≫
        Functor.leftUnitor _ := by
  subst he
  subst hc
  rw [frobeniusColimitPullbackIdOfEq_self]
  exact (Iso.trans_refl _).trans
    ((frobeniusColimitPullbackCompOfEq_self p f (𝟙 Y) hX hY hY _ b).trans
    (_root_.SheafOfModules.pullback_id_comp.{u} b))

/-- **The right unit coherence.** For `e` equal to the identity of `colim_F 𝒪_X`, the comparison
of the transition functors of `𝟙 X` and of `f` is the identity comparison of `𝟙 X` whiskered into
the transition functor of `f`.

Both the morphism `c` attached to the composite `𝟙 X ≫ f` and the identification of extension of
scalars along it with extension of scalars along `a` are parameters, for the reason recorded at
`AlgebraicGeometry.frobeniusColimitPullbackIdOfEq_comp`. -/
lemma frobeniusColimitPullbackCompOfEq_id (f : X ⟶ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (e : frobeniusColimitRingSheaf X p hX ⟶
      ((𝟙 X : X ⟶ X).ringSheafPushforward).obj (frobeniusColimitRingSheaf X p hX))
    (he : e = 𝟙 (frobeniusColimitRingSheaf X p hX))
    (a : frobeniusColimitRingSheaf Y p hY ⟶
      (f.ringSheafPushforward).obj (frobeniusColimitRingSheaf X p hX))
    (c : frobeniusColimitRingSheaf Y p hY ⟶
      ((𝟙 X ≫ f).ringSheafPushforward).obj (frobeniusColimitRingSheaf X p hX))
    (hc : c = a ≫ (f.ringSheafPushforward).map e)
    (hFE : _root_.SheafOfModules.pullback.{u} c = _root_.SheafOfModules.pullback.{u} a) :
    frobeniusColimitPullbackCompOfEq p (𝟙 X) f hX hX hY a e c hc ≪≫ eqToIso hFE =
      Functor.isoWhiskerLeft (_root_.SheafOfModules.pullback.{u} a)
          (frobeniusColimitPullbackIdOfEq X p hX e he) ≪≫
        Functor.rightUnitor _ := by
  subst he
  subst hc
  rw [frobeniusColimitPullbackIdOfEq_self]
  exact (Iso.trans_refl _).trans
    ((frobeniusColimitPullbackCompOfEq_self p (𝟙 X) f hX hX hY a _).trans
    (_root_.SheafOfModules.pullback_comp_id.{u} a))

/-- The transition functor of the identity of `X` is the identity functor of the category of
finite locally free `colim_F 𝒪_X`-modules. -/
noncomputable def frobeniusColimitVectorBundlesPullbackId (X : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hX : IsInCharacteristic X p) :
    frobeniusColimitVectorBundlesPullback p (𝟙 X) hX hX ≅
      𝟭 (frobeniusColimitVectorBundles X p hX) :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ ((frobeniusColimitPullbackId X p hX).app M.1))
    (fun {_ _} φ => (ObjectProperty.ι _).map_injective
      ((frobeniusColimitPullbackId X p hX).hom.naturality φ.hom))

/-- The transition functor of `g` followed by that of `f` is the transition functor of `f ≫ g`,
on the categories of finite locally free modules over the Frobenius colimits. -/
noncomputable def frobeniusColimitVectorBundlesPullbackComp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (hZ : IsInCharacteristic Z p) :
    frobeniusColimitVectorBundlesPullback p g hY hZ ⋙
        frobeniusColimitVectorBundlesPullback p f hX hY ≅
      frobeniusColimitVectorBundlesPullback p (f ≫ g) hX hZ :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _
      ((frobeniusColimitPullbackComp p f g hX hY hZ).app M.1))
    (fun {_ _} φ => (ObjectProperty.ι _).map_injective
      ((frobeniusColimitPullbackComp p f g hX hY hZ).hom.naturality φ.hom))

end AlgebraicGeometry

end
