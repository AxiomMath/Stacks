module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.MemberDatumKernel

/-!
# The quasi-coherent descent datum of Stacks 03DX (1), through the invariant presentation

`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/MemberDatumPackaging.lean` and
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/MemberDatumKernel.lean` prove the object
family, the transition isomorphisms and both laws of the descent datum of Stacks 03DX (1) for a
family of objects of `(Sch/S)_fppf`, in the spelling of
`CategoryTheory.Pseudofunctor.DescentData'` on the fibre products of the site read downstairs.
What they do not do is assemble them: their implementation notes record that the constructor
application exceeds the kernel's budget.  **This file assembles them.**

Two changes make the assembly affordable.

First, the datum is built in Mathlib's *invariant* presentation
`CategoryTheory.Pseudofunctor.DescentData` — the transitions indexed by every scheme mapping to
two members of the family — rather than in `CategoryTheory.Pseudofunctor.DescentData'`.  Its
three laws are phrased with the plain
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` and with their own bound
morphisms, so no projection of a chosen pullback and no autoparameter proof baked in by a
structure declaration occurs in a field type; the data and the laws are supplied by the three
Mathlib lemmas `CategoryTheory.Pseudofunctor.DescentData'.pullHom_pullHom'`,
`…pullHom'_self'` and `…comp_pullHom''`, which take the chosen-pullback laws as hypotheses.  The
primed datum is then obtained from it by `CategoryTheory.Pseudofunctor.DescentData'`
`.ofDescentData`, which is a function application and not a structure instance, so the two
primed law fields are never elaborated at these pullbacks at all.  The invariant presentation is
in any case the one the consumer wants: `AlgebraicGeometry.QuasicoherentDescentData` is by
definition the full subcategory of `CategoryTheory.Pseudofunctor.DescentData` on quasi-coherent
components.

Second — and this is what the earlier diagnosis missed — the family of schemes and of structure
morphisms is **pinned under names of its own**,
`AlgebraicGeometry.BigFppfOver.memberScheme` and
`AlgebraicGeometry.BigFppfOver.memberStructureHom`, and the chosen pullbacks are restated at
those names.  `AlgebraicGeometry.BigFppfOver.objScheme` and `…objHom` are `abbrev`s, so a family
built from them instantiates the `X : ι → C` and `f : ∀ i, X i ⟶ S` parameters of every lemma
above with a *reducible lambda*; the kernel then unfolds it, and through it the canonical functor
to schemes, inside the categories of sheaves of modules the law speaks about.  On the
cocycle law alone: with the family spelled `fun i => objScheme B S hS (X i)` the kernel exceeds
its 200 000-heartbeat budget (and the elaborator spends ~60 s); with every other ingredient of
the statement left abstract and only that family pinned to a `def`, the same application is
checked in about three seconds.  The autoparameter proofs are
*not* the cost: with the family pinned, the laws go through with the structure's own proof terms,
and with the family unpinned they fail even when the proof terms match syntactically and even
when the chosen pullbacks are abstract variables.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.memberScheme` and
  `AlgebraicGeometry.BigFppfOver.memberStructureHom`: the family of schemes of the members of the
  family and their structure morphisms, under names of their own.
* `AlgebraicGeometry.BigFppfOver.memberHypercover`: that family as a
  `CategoryTheory.PreZeroHypercover` of `S`.
* `AlgebraicGeometry.BigFppfOver.memberChosenPullbackPin` and
  `AlgebraicGeometry.BigFppfOver.memberChosenPullback₃Pin`: the fibre products of two and of
  three members, read as chosen pullbacks of the pinned structure morphisms.
* `AlgebraicGeometry.BigFppfOver.memberDatum`: **the descent datum of Stacks 03DX (1)** for the
  pullback pseudofunctor of sheaves of modules, in Mathlib's invariant presentation.
* `AlgebraicGeometry.BigFppfOver.memberDatumPrime`: the same datum on the chosen fibre products
  — the term `MemberDatumPackaging` could not build.
* `AlgebraicGeometry.BigFppfOver.memberQcohDatum`: **the quasi-coherent descent datum** of
  Stacks 03DX (1) for the family of structure morphisms of the members.

## Main results

* `Stacks.pullHom'_self_of_self` and `Stacks.comp_pullHom'_of_comp`: the identity and cocycle
  laws of a chosen-pullback datum, read at an arbitrary object mapping to the members.  They are
  `CategoryTheory.Pseudofunctor.DescentData'.pullHom'_self'` and `…comp_pullHom''` with their
  hypotheses restated so that the autoparameter proofs are
  `CategoryTheory.Limits.ChosenPullback₃.w₁` and its companions and the conclusion's are the
  bound hypotheses themselves; both restatements happen where the chosen pullbacks are abstract
  variables, hence where no proof can be unfolded.
* `AlgebraicGeometry.BigFppfOver.memberHomSelfPin` and
  `AlgebraicGeometry.BigFppfOver.memberHomCompPin`: the two laws of
  `MemberDatumPackaging`/`MemberDatumKernel` at the pinned chosen pullbacks.
* `AlgebraicGeometry.BigFppfOver.memberDatum_hom_eq_transitionIso` and
  `AlgebraicGeometry.BigFppfOver.memberDatumPrime_hom`: the transitions of the datum are the
  transition isomorphisms of Stacks 03DX (1) — at every object of the site mapping to two members
  of the family, and over the chosen fibre products respectively.  This is what says the term
  built here is the datum of Stacks 03DX (1).
* `AlgebraicGeometry.BigFppfOver.memberQcohDatum_component`: the components of the
  quasi-coherent datum are the local modules of Stacks 03DV themselves.
* `AlgebraicGeometry.BigFppfOver.memberHypercover_presieve₀`: the pinned family generates the
  same presieve as `AlgebraicGeometry.BigFppfOver.objHypercover`, so the fpqc hypothesis on one
  is the fpqc hypothesis on the other.

## Implementation notes

Nothing here carries a `stacks` attribute.  Every definition below used to be parametrized by
`AlgebraicGeometry.BigFppfOver.LocalComparisonPseudonatural`, the pseudonaturality of the
comparison isomorphism of Stacks 03DV; that is now a theorem,
`AlgebraicGeometry.BigFppfOver.localComparisonPseudonatural`, and the hypothesis has been struck
from every declaration here and replaced by an application of it.  **The datum of Stacks 03DX (1)
is therefore unconditional.**  What keeps the tag off this file is what the next paragraph
describes, not a hypothesis of the declarations below.

What this file does **not** do is discharge
`AlgebraicGeometry.BigFppfOver.AssociatedModuleGlueDescentDatum` or
`…AssociatedModuleRefinedDatum`.  Those ask for more than the datum: from the effectivity of the
datum they want a quasi-coherent `𝓕` on `S` *together with* isomorphisms
`𝓕^a|_{X i} ≅ 𝒢|_{X i}` in the relocalization spelling of
`AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_forall_memberProd`, agreeing over
the fibre products.  Transporting the component isomorphisms of an effectivity witness —
`(objHom (X i))^* 𝓕 ≅ F i` — through Stacks 03DV to that spelling is the step that remains, and
it is independent of the performance considerations above.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 023B](https://stacks.math.columbia.edu/tag/023B)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
  CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
  CategoryTheory.Pseudofunctor.DescentData'

universe t v' v u' u w

namespace Stacks

variable {C : Type u} [Category.{v} C]
  {F : CategoryTheory.Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  {sq : ∀ i j, ChosenPullback (f i) (f j)}
  {sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃)}
  {obj : ∀ (i : ι), F.obj (.mk (op (X i)))}
  (hom : ∀ (i j : ι), (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))

/-- **The identity law of a chosen-pullback datum, read at an arbitrary object.**  This is
`CategoryTheory.Pseudofunctor.DescentData'.pullHom'_self'` with the hypothesis restated so that
the two autoparameter proofs of `𝟙 _ ≫ f i = f i` are `CategoryTheory.Category.id_comp`, the
spelling the laws of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/MemberDatumPackaging.lean` are proved in,
and the conclusion's are the bound hypothesis itself, the spelling the field
`CategoryTheory.Pseudofunctor.DescentData.hom_self` asks for.

The restatement is made here, where `sq` is an abstract variable: comparing the two spellings of
such a proof at a concrete chosen pullback is what no budget affords, and against an abstract
variable there is nothing to unfold. -/
public theorem pullHom'_self_of_self
    (hs : ∀ i, pullHom' hom (f i) (𝟙 (X i)) (𝟙 (X i)) (Category.id_comp _) (Category.id_comp _)
      = 𝟙 _)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (hg : g ≫ f i = q) :
    pullHom' hom q g g hg hg = 𝟙 _ :=
  pullHom'_self' hom hs q g hg

/-- **The cocycle law of a chosen-pullback datum, read at an arbitrary object.**  This is
`CategoryTheory.Pseudofunctor.DescentData'.comp_pullHom''` with the hypothesis restated so that
the six autoparameter proofs over the chosen threefold product are
`CategoryTheory.Limits.ChosenPullback₃.w₁`, `.w₂` and `.w₃` — the spelling
`AlgebraicGeometry.BigFppfOver.pullHom'_memberTransition_comp` is proved in — and so that the
conclusion's are the bound hypotheses themselves, the spelling the field
`CategoryTheory.Pseudofunctor.DescentData.hom_comp` asks for.

As for the identity law, the restatement is made where `sq` and `sq₃` are abstract variables. -/
public theorem comp_pullHom'_of_comp
    (hc : ∀ (i₁ i₂ i₃ : ι),
      pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂
          (sq₃ i₁ i₂ i₃).w₁ (sq₃ i₁ i₂ i₃).w₂ ≫
        pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃
          (sq₃ i₁ i₂ i₃).w₂ (sq₃ i₁ i₂ i₃).w₃ =
      pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃
        (sq₃ i₁ i₂ i₃).w₁ (sq₃ i₁ i₂ i₃).w₃)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
    pullHom' hom q f₁ f₂ hf₁ hf₂ ≫ pullHom' hom q f₂ f₃ hf₂ hf₃ =
      pullHom' hom q f₁ f₃ hf₁ hf₃ :=
  comp_pullHom'' (sq₃ := sq₃) hom hc q f₁ f₂ f₃ hf₁ hf₂ hf₃

end Stacks

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {I : Type w} (X : I → BigFppfOver B S hS)

/-! ### The family of schemes, pinned -/

/-- **The scheme of a member of a family of objects of `(Sch/S)_fppf`, under a name of its
own.**  This is `AlgebraicGeometry.BigFppfOver.objScheme` at `X i` and nothing else; the point of
naming it is that `objScheme` is an `abbrev`, so a family built directly from it is a reducible
lambda, and every lemma about descent data instantiated at such a family is re-checked by
unfolding it — through `AlgebraicGeometry.BigFppfOver.toScheme` — inside categories of sheaves of
modules.  See the implementation notes for the measurement. -/
public noncomputable def memberScheme (i : I) : Scheme.{u} := objScheme B S hS (X i)

/-- **The structure morphism of a member of the family, under a name of its own**: the morphism
`AlgebraicGeometry.BigFppfOver.objHom` of the member, read as a morphism out of
`AlgebraicGeometry.BigFppfOver.memberScheme`.  This is the family of morphisms relative to which
the descent datum of Stacks 03DX (1) is a descent datum. -/
public noncomputable def memberStructureHom (i : I) : memberScheme B S hS X i ⟶ S :=
  objHom B S hS (X i)

/-- **The family of structure morphisms of the members, as a covering family of `S`.**  It is
`AlgebraicGeometry.BigFppfOver.objHypercover` with its two families pinned, which is the shape in
which `AlgebraicGeometry.QuasicoherentDescentData` consumes a covering family without re-checking
the laws of the datum through the unfolding of `objScheme`. -/
public noncomputable def memberHypercover : PreZeroHypercover.{w} S :=
  ⟨I, memberScheme B S hS X, memberStructureHom B S hS X⟩

/-- **The pinned family generates the same presieve of `S`** as
`AlgebraicGeometry.BigFppfOver.objHypercover` does: the two differ only in the names the two
families are written with.  So the hypothesis that the structure morphisms of the members are an
fpqc covering family of `S` is the same hypothesis on either. -/
public theorem memberHypercover_presieve₀ :
    (memberHypercover B S hS X).presieve₀ = (objHypercover B S hS X).presieve₀ := rfl

/-- **The fibre product of two members of the family, read as a chosen pullback of the pinned
structure morphisms.**  It is `AlgebraicGeometry.BigFppfOver.memberChosenPullback`, restated at
`AlgebraicGeometry.BigFppfOver.memberStructureHom`. -/
public noncomputable def memberChosenPullbackPin (i j : I) :
    ChosenPullback (memberStructureHom B S hS X i) (memberStructureHom B S hS X j) :=
  memberChosenPullback B S hS X i j

/-- **The threefold fibre product of three members of the family, read as a chosen threefold
wide pullback of the pinned structure morphisms.**  It is
`AlgebraicGeometry.BigFppfOver.memberChosenPullback₃`, restated at
`AlgebraicGeometry.BigFppfOver.memberChosenPullbackPin`. -/
public noncomputable def memberChosenPullback₃Pin (i₁ i₂ i₃ : I) :
    ChosenPullback₃ (memberChosenPullbackPin B S hS X i₁ i₂)
      (memberChosenPullbackPin B S hS X i₂ i₃) (memberChosenPullbackPin B S hS X i₁ i₃) :=
  memberChosenPullback₃ B S hS X i₁ i₂ i₃

variable (G : SheafOfModules.{u} (structureSheaf B S hS))
  (F : ∀ i, (objScheme B S hS (X i)).Modules)
  (hF : ∀ i, (F i).IsQuasicoherent)
  (e : ∀ i, (associatedModule B (objScheme B S hS (X i))
    (contains_objScheme B S hS (X i))).obj (F i) ≅ (objRestrict B S hS (X i)).obj G)

/-! ### The two laws at the pinned chosen pullbacks -/

/-- **The identity law of the descent datum at the pinned chosen pullbacks.**  This is
`AlgebraicGeometry.BigFppfOver.memberHom_self_law`, whose statement it is after the structure
morphisms of the members have been renamed. -/
public theorem memberHomSelfPin (i : I) :
    pullHom' (sq := memberChosenPullbackPin B S hS X) (obj := memberObj B S hS X F)
      (obj' := memberObj B S hS X F) (memberHom B S hS G X F hF e)
      (memberStructureHom B S hS X i) (𝟙 (memberScheme B S hS X i))
      (𝟙 (memberScheme B S hS X i)) (Category.id_comp _) (Category.id_comp _) = 𝟙 _ :=
  memberHom_self_law B S hS G X F hF e i

/-- **A transition of the chosen-pullback datum is the transition isomorphism of Stacks 03DX (1)**
at any pair of morphisms `(a₁, a₂)` that factors through the fibre product of the members. -/
private theorem pullHom'_pin_eq_transitionIso
    {i₁ i₂ : I} {Z : BigFppfOver B S hS} (m : Z ⟶ memberProd B S hS X i₁ i₂)
    {a₁ : Z ⟶ X i₁} (ha₁ : m ≫ memberProdFst B S hS X i₁ i₂ = a₁)
    {a₂ : Z ⟶ X i₂} (ha₂ : m ≫ memberProdSnd B S hS X i₁ i₂ = a₂)
    (q : objScheme B S hS Z ⟶ S)
    (hf₁ : objHomOver B S hS a₁ ≫ memberStructureHom B S hS X i₁ = q)
    (hf₂ : objHomOver B S hS a₂ ≫ memberStructureHom B S hS X i₂ = q) :
    pullHom' (sq := memberChosenPullbackPin B S hS X) (obj := memberObj B S hS X F)
        (obj' := memberObj B S hS X F) (memberHom B S hS G X F hF e) q
        (objHomOver B S hS a₁) (objHomOver B S hS a₂) hf₁ hf₂ =
      (transitionIso B S hS G a₁ a₂ (hF i₁) (e i₁) (hF i₂) (e i₂)).hom :=
  (pullHom'_eq_pullHom (sq := memberChosenPullbackPin B S hS X) (obj := memberObj B S hS X F)
      (obj' := memberObj B S hS X F) (memberHom B S hS G X F hF e) q _ _
      (objHomOver B S hS m) hf₁ hf₂ (by subst ha₁; rfl) (by subst ha₂; rfl)).trans
    (pullHom_eq_transitionIso B S hS G (localComparisonPseudonatural B S hS G) m
      (memberProdFst B S hS X i₁ i₂)
      (memberProdSnd B S hS X i₁ i₂) ha₁ ha₂ (hF i₁) (e i₁) (hF i₂) (e i₂))

/-- **The cocycle law of the descent datum at the pinned chosen pullbacks.**  The three
transports along the projections of the threefold fibre product compose.

The proof is `AlgebraicGeometry.BigFppfOver.pullHom'_memberTransition_comp`'s, carried out at the
pinned chosen pullbacks and in the spelling of
`AlgebraicGeometry.BigFppfOver.memberHom`: each `pullHom'` is reduced to a `pullHom` along the
projection of the threefold product of the *site* by
`CategoryTheory.Pseudofunctor.DescentData'.pullHom'_eq_pullHom`, each of those is the transition
isomorphism of Stacks 03DX (1) at the corresponding pair of projections by
`AlgebraicGeometry.BigFppfOver.pullHom_eq_transitionIso`, and the three compose by
`AlgebraicGeometry.BigFppfOver.transitionIso_trans`.  The two reductions are performed by
`Stacks.comp_eq_of_eq`, whose own types are small. -/
public theorem memberHomCompPin (i₁ i₂ i₃ : I) :
    pullHom' (sq := memberChosenPullbackPin B S hS X) (obj := memberObj B S hS X F)
          (obj' := memberObj B S hS X F) (memberHom B S hS G X F hF e)
          (memberChosenPullback₃Pin B S hS X i₁ i₂ i₃).p
          (memberChosenPullback₃Pin B S hS X i₁ i₂ i₃).p₁
          (memberChosenPullback₃Pin B S hS X i₁ i₂ i₃).p₂
          (memberChosenPullback₃Pin B S hS X i₁ i₂ i₃).w₁
          (memberChosenPullback₃Pin B S hS X i₁ i₂ i₃).w₂ ≫
        pullHom' (sq := memberChosenPullbackPin B S hS X) (obj := memberObj B S hS X F)
          (obj' := memberObj B S hS X F) (memberHom B S hS G X F hF e)
          (memberChosenPullback₃Pin B S hS X i₁ i₂ i₃).p
          (memberChosenPullback₃Pin B S hS X i₁ i₂ i₃).p₂
          (memberChosenPullback₃Pin B S hS X i₁ i₂ i₃).p₃
          (memberChosenPullback₃Pin B S hS X i₁ i₂ i₃).w₂
          (memberChosenPullback₃Pin B S hS X i₁ i₂ i₃).w₃ =
      pullHom' (sq := memberChosenPullbackPin B S hS X) (obj := memberObj B S hS X F)
        (obj' := memberObj B S hS X F) (memberHom B S hS G X F hF e)
        (memberChosenPullback₃Pin B S hS X i₁ i₂ i₃).p
        (memberChosenPullback₃Pin B S hS X i₁ i₂ i₃).p₁
        (memberChosenPullback₃Pin B S hS X i₁ i₂ i₃).p₃
        (memberChosenPullback₃Pin B S hS X i₁ i₂ i₃).w₁
        (memberChosenPullback₃Pin B S hS X i₁ i₂ i₃).w₃ := by
  exact Stacks.comp_eq_of_eq
    (pullHom'_pin_eq_transitionIso B S hS X G F hF e
      (pullback.fst (memberProdSnd B S hS X i₁ i₂) (memberProdFst B S hS X i₂ i₃))
      (a₁ := memberProd₃Fst B S hS X i₁ i₂ i₃) rfl
      (a₂ := memberProd₃Mid B S hS X i₁ i₂ i₃) rfl _ _ _)
    (pullHom'_pin_eq_transitionIso B S hS X G F hF e
      (pullback.snd (memberProdSnd B S hS X i₁ i₂) (memberProdFst B S hS X i₂ i₃))
      (a₁ := memberProd₃Mid B S hS X i₁ i₂ i₃) pullback.condition.symm
      (a₂ := memberProd₃Snd B S hS X i₁ i₂ i₃) rfl _ _ _)
    (pullHom'_pin_eq_transitionIso B S hS X G F hF e
      (memberProd₃Outer B S hS X i₁ i₂ i₃)
      (a₁ := memberProd₃Fst B S hS X i₁ i₂ i₃) (pullback.lift_fst _ _ _)
      (a₂ := memberProd₃Snd B S hS X i₁ i₂ i₃) (pullback.lift_snd _ _ _) _ _ _)
    (transitionIso_trans B S hS G (memberProd₃Fst B S hS X i₁ i₂ i₃)
      (memberProd₃Mid B S hS X i₁ i₂ i₃) (memberProd₃Snd B S hS X i₁ i₂ i₃)
      (hF i₁) (e i₁) (hF i₂) (e i₂) (hF i₃) (e i₃))

/-! ### The datum -/

/-- **The descent datum of Stacks 03DX (1), in Mathlib's invariant presentation.**  For a family
of objects of `(Sch/S)_fppf` on whose members the restriction of `𝒢` is the associated module of
a quasi-coherent sheaf, this is the descent datum for
`AlgebraicGeometry.modulePullbackPseudofunctor` relative to the family of structure morphisms of
the members: the local modules of Stacks 03DV as objects, and over every scheme mapping to two
members the transition isomorphism of Stacks 03DX (1) transported there.

The transition over an arbitrary pair `(f₁, f₂)` is the chosen-pullback transition
`AlgebraicGeometry.BigFppfOver.memberHom` transported through the fibre product by
`CategoryTheory.Pseudofunctor.DescentData'.pullHom'`.  That is what makes the datum available at
schemes which are not objects of the site at all, which the invariant presentation requires and
the site cannot supply: `𝒢` can only be restricted to an object of `(Sch/S)_fppf`.

Its three laws are the three Mathlib lemmas that take the chosen-pullback laws as hypotheses —
`CategoryTheory.Pseudofunctor.DescentData'.pullHom_pullHom'`, which needs no law at all, and
`Stacks.pullHom'_self_of_self` and `Stacks.comp_pullHom'_of_comp`, fed
`AlgebraicGeometry.BigFppfOver.memberHomSelfPin` and
`AlgebraicGeometry.BigFppfOver.memberHomCompPin`. -/
public noncomputable def memberDatum :
    modulePullbackPseudofunctor.DescentData (memberStructureHom B S hS X) where
  obj := memberObj B S hS X F
  hom _ q _ _ f₁ f₂ hf₁ hf₂ :=
    pullHom' (sq := memberChosenPullbackPin B S hS X) (obj := memberObj B S hS X F)
      (obj' := memberObj B S hS X F) (memberHom B S hS G X F hF e) q f₁ f₂ hf₁ hf₂
  pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    pullHom_pullHom' (sq := memberChosenPullbackPin B S hS X) (obj := memberObj B S hS X F)
      (obj' := memberObj B S hS X F) (memberHom B S hS G X F hF e)
      g q q' f₁ f₂ gf₁ gf₂ hq hf₁ hf₂ hgf₁ hgf₂
  hom_self _ q _ g hg :=
    Stacks.pullHom'_self_of_self (sq := memberChosenPullbackPin B S hS X)
      (obj := memberObj B S hS X F) (memberHom B S hS G X F hF e)
      (fun i => memberHomSelfPin B S hS X G F hF e i) q g hg
  hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
    Stacks.comp_pullHom'_of_comp (sq := memberChosenPullbackPin B S hS X)
      (sq₃ := memberChosenPullback₃Pin B S hS X) (obj := memberObj B S hS X F)
      (memberHom B S hS G X F hF e)
      (fun i₁ i₂ i₃ => memberHomCompPin B S hS X G F hF e i₁ i₂ i₃)
      q f₁ f₂ f₃ hf₁ hf₂ hf₃

/-- **The descent datum of Stacks 03DX (1) on the chosen fibre products.**  This is the term
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/MemberDatumPackaging.lean` reduces to its
two laws and cannot assemble: `CategoryTheory.Pseudofunctor.DescentData'` at the fibre products of
the big fppf site read downstairs.

It is obtained from `AlgebraicGeometry.BigFppfOver.memberDatum` by
`CategoryTheory.Pseudofunctor.DescentData'.ofDescentData`, which discharges the two primed law
fields by its own tactic proofs at the general level.  Being a function application and not a
structure instance, it never elaborates a primed field type at these pullbacks, which is what the
constructor application could not afford. -/
public noncomputable def memberDatumPrime :
    modulePullbackPseudofunctor.DescentData' (memberChosenPullbackPin B S hS X)
      (memberChosenPullback₃Pin B S hS X) :=
  ofDescentData (memberChosenPullbackPin B S hS X) (memberChosenPullback₃Pin B S hS X)
    (memberDatum B S hS X G F hF e)

/-- **The transitions of the datum are the transition isomorphisms of Stacks 03DX (1)**, at
every object of the site mapping to two members of the family: if `m : Z ⟶ X i₁ ×_S X i₂` has
composites `a₁` and `a₂` with the two projections, then the transition of
`AlgebraicGeometry.BigFppfOver.memberDatum` at the pair `(a₁, a₂)` read downstairs is
`AlgebraicGeometry.BigFppfOver.transitionIso` at `(a₁, a₂)` itself.

This is `AlgebraicGeometry.BigFppfOver.pullHom'_memberTransition` at the pinned chosen pullbacks,
and it is the statement that the datum is the datum of Stacks 03DX (1) and not merely *a* datum:
the transport through the chosen fibre product that defines
`AlgebraicGeometry.BigFppfOver.memberDatum`'s `hom` field introduces nothing, because the chosen
fibre products are fibre products of the site and every pair of morphisms into two members
factors through one. -/
public theorem memberDatum_hom_eq_transitionIso
    {i₁ i₂ : I} {Z : BigFppfOver B S hS} (m : Z ⟶ memberProd B S hS X i₁ i₂)
    {a₁ : Z ⟶ X i₁} (ha₁ : m ≫ memberProdFst B S hS X i₁ i₂ = a₁)
    {a₂ : Z ⟶ X i₂} (ha₂ : m ≫ memberProdSnd B S hS X i₁ i₂ = a₂)
    (q : objScheme B S hS Z ⟶ S)
    (hf₁ : objHomOver B S hS a₁ ≫ memberStructureHom B S hS X i₁ = q)
    (hf₂ : objHomOver B S hS a₂ ≫ memberStructureHom B S hS X i₂ = q) :
    (memberDatum B S hS X G F hF e).hom q (objHomOver B S hS a₁) (objHomOver B S hS a₂)
        hf₁ hf₂ =
      (transitionIso B S hS G a₁ a₂ (hF i₁) (e i₁) (hF i₂) (e i₂)).hom :=
  pullHom'_pin_eq_transitionIso B S hS X G F hF e m ha₁ ha₂ q hf₁ hf₂

/-- **The transition of the primed datum over the chosen fibre product of two members is
`AlgebraicGeometry.BigFppfOver.memberHom`**, the `hom` field
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/MemberDatumPackaging.lean` pinned for the
constructor it could not apply.  So passing through the invariant presentation changes the datum
in no way. -/
public theorem memberDatumPrime_hom (i j : I) :
    (memberDatumPrime B S hS X G F hF e).hom i j = memberHom B S hS G X F hF e i j :=
  pullHom'_p₁_p₂ (sq := memberChosenPullbackPin B S hS X) (obj := memberObj B S hS X F)
    (memberHom B S hS G X F hF e) i j

/-- **The quasi-coherent descent datum of Stacks 03DX (1).**  The components of
`AlgebraicGeometry.BigFppfOver.memberDatum` are the local modules of Stacks 03DV, which are
quasi-coherent by hypothesis, so the datum lies in the full subcategory
`AlgebraicGeometry.QuasicoherentDescentData` of Stacks 023B on quasi-coherent components.

This is the datum that the effectivity half of Stacks 023T consumes. -/
public noncomputable def memberQcohDatum :
    QuasicoherentDescentData (memberStructureHom B S hS X) :=
  ⟨memberDatum B S hS X G F hF e, fun i => hF i⟩

/-- **The components of the quasi-coherent datum are the local modules of Stacks 03DV**
themselves, with no transport. -/
public theorem memberQcohDatum_component (i : I) :
    (memberQcohDatum B S hS X G F hF e).component i = F i := rfl

/-- **The quasi-coherent datum, read on the pinned covering family of `S`.**  The family of
morphisms of `AlgebraicGeometry.BigFppfOver.memberHypercover` is the pinned family of structure
morphisms, so this is `AlgebraicGeometry.BigFppfOver.memberQcohDatum` with nothing changed; it is
the shape in which `AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage` —
the effectivity half of Stacks 023T — asks for a datum. -/
public noncomputable def memberHypercoverQcohDatum :
    QuasicoherentDescentData (memberHypercover B S hS X).f :=
  memberQcohDatum B S hS X G F hF e

end AlgebraicGeometry.BigFppfOver

end
