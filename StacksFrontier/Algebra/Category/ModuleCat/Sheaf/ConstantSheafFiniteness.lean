module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Limits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.CategoryTheory.Sites.Sheafification.LocalRepresentatives

/-!
# Finiteness of constant sheaves of modules

Let `(C, J)` be a site, `R` a ring and `M` an `R`-module. The constant sheaf of rings `R̲` is the
sheafification of the constant presheaf with value `R`, and the constant sheaf of modules `M̲` is
the sheafification of the constant presheaf of modules with value `M`, regarded as a sheaf of
`R̲`-modules. Stacks Tag 093N says that if the topos of sheaves on `C` is not empty, then

1. `M̲` is of finite type if and only if `M` is a finite `R`-module, and
2. `M̲` is of finite presentation if and only if `M` is a finitely presented `R`-module.

This file proves part (1), builds the exactness theory of the constant sheaf of modules functor,
and proves the forward implication of part (2). The converse implication of part (2) and the
resulting equivalence are in `StacksDraft.Ch18.Sec42.Tag093N`.

Non-emptiness of the topos is expressed, as in the source, by the existence of an object which is
not sheaf theoretically empty, i.e. an object `U` whose empty sieve is not a covering sieve
(Sites, Definition 04B5); this avoids any smallness hypothesis on the site.

## Main definitions

* `Stacks.SheafOfModules.Constant.constantModulePresheaf`: the constant presheaf of modules with
  value `M` over the constant presheaf of rings with value `R`.
* `Stacks.SheafOfModules.Constant.constantModuleSheaf`: the constant sheaf of modules `M̲`, as a
  sheaf of modules over the constant sheaf of rings `R̲`, together with its functoriality
  `constantModuleSheafMap` and the packaged functor `constantModuleSheafFunctor`.
* `Stacks.SheafOfModules.Constant.constantSectionOver` and
  `Stacks.SheafOfModules.Constant.constantValue`: the section of `M̲` over the slice site `C/U`
  determined by an element of `M`, and its value over an object.
* `Stacks.SheafOfModules.Constant.toSheafConstantIso`: the underlying abelian sheaf of `M̲` is the
  constant abelian sheaf on the underlying abelian group of `M`.
* `Stacks.SheafOfModules.Constant.constantUnitHomEquiv`: the corepresentability of global sections
  by `R̲` viewed as a sheaf of modules over itself.

## Main results

* `Stacks.SheafOfModules.Constant.constantModuleSheaf_isFiniteType_iff`: **Stacks Tag 093N, part
  (1)**. On a site with a non sheaf theoretically empty object, `M̲` is of finite type if and only
  if `M` is a finite `R`-module. The two halves are
  `Stacks.SheafOfModules.Constant.isFiniteType_of_finite` and
  `Stacks.SheafOfModules.Constant.finite_of_generatingSections`.
* `Stacks.SheafOfModules.Constant.preservesFiniteLimits_constantModuleSheafFunctor` and
  `Stacks.SheafOfModules.Constant.preservesFiniteColimits_constantModuleSheafFunctor`: the
  constant sheaf of modules functor is exact.
* `Stacks.SheafOfModules.Constant.unitIsoConstantModuleSheaf`: `SheafOfModules.unit R̲ ≅ R̲` as a
  constant sheaf of modules; both corepresent global sections.
* `Stacks.SheafOfModules.Constant.freeIsoConstantModuleSheaf` and
  `Stacks.SheafOfModules.Constant.freeIsoPi`: for a finite index type `I`,
  `SheafOfModules.free I ≅ (⨿_I R)̲ ≅ (I → R)̲`, the constant sheaf of modules on the free module
  on `I`.
* `Stacks.SheafOfModules.Constant.epi_constantModuleSheafMap` and
  `Stacks.SheafOfModules.Constant.kernelIsoConstant`: the constant sheaf functor takes
  epimorphisms to epimorphisms and commutes with kernels.
* `Stacks.SheafOfModules.Constant.finitePresentation_of_isFinitePresentation`: **Stacks Tag 093N,
  part (2), the forward implication**. If `M̲` is of finite presentation then `M` is a finitely
  presented `R`-module.
* `Stacks.SheafOfModules.Constant.exists_cover_representatives`: finitely many sections of the
  target of a locally surjective morphism of abelian presheaves have simultaneous local
  representatives on a covering family none of whose members is sheaf theoretically empty. This
  is what turns the local data produced by `IsFiniteType` into elements of `M`.
* `Stacks.SheafOfModules.Constant.reflectsIsomorphisms_toSheaf`: `SheafOfModules.toSheaf` reflects
  isomorphisms.

## Implementation notes

**Universes.** The site (`u`, `v`) and the module universe (`w`) stay independent, as in the
source statement; `w` is the universe of the ring, of the modules and of the sheaves of modules
throughout, which is the generality in which Mathlib states `SheafOfModules.IsFiniteType`.
Nothing is specialised.

**Hypotheses.** Only `HasWeakSheafify` and `GrothendieckTopology.WEqualsLocallyBijective` for
`RingCat.{w}` and `AddCommGrpCat.{w}`, on `J` and on the slice topologies `J.over U`, are
assumed. These are exactly what is needed to *state* that `M̲` is a sheaf of modules over `R̲` and
that it is of finite type. Left exactness of abelian sheafification, i.e.
`HasSheafify J AddCommGrpCat.{w}`, is **derived** rather than assumed, from
`AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective` (Tag 03DB); it is therefore
introduced with `have` at each of the few places it is needed and never appears in a statement.

**Local surjectivity at an unrelated module universe.** The proof needs
`Presheaf.IsLocallySurjective J (toSheafify J P)` for `P` an abelian presheaf whose values lie in
`Type w` with `w` unrelated to `max u v`. Mathlib's instance `isLocallySurjective_toSheafify'`
requires the values to lie in `Type (max u v)`, but the instance in
`Mathlib/CategoryTheory/Sites/LocallyBijective.lean` deduces both local injectivity and local
surjectivity of `toSheafify` from `J.WEqualsLocallyBijective` with no universe restriction, and
that hypothesis is already part of the statement. So no separate construction is needed.

**Why the proof of part (1) is not symmetric.** The easy half constructs, from a finite spanning
family of `M`, a family of global sections of `M̲` restricted to each slice site, and checks that
the induced morphism from a free sheaf of modules is an epimorphism; the free index type is the
spanning family, and the covering family of the terminal object is the trivial one indexed by all
of `C` (`isFiniteType_of_finite`). The hard half starts from an arbitrary family of local
generators, has to replace the local sections by *constant* ones on a refinement
(`exists_cover_representatives`), and has to know that over a non sheaf theoretically empty
object distinct elements of `M` stay distinct (`constant_section_injective`). It then shows the
quotient of `M` by the span of the chosen elements has vanishing constant sheaf, which forces the
span to be everything.

**Exactness of the constant sheaf functor.** `constantModuleSheafFunctor` is exact, and this is
proved by reduction to the abelian case rather than by hand: composing with
`SheafOfModules.toSheaf` gives, *on the nose*, the composite of the forgetful functor
`ModuleCat R ⥤ AddCommGrpCat` with the constant abelian sheaf functor. Both factors of the latter
are exact, and `SheafOfModules.toSheaf` preserves limits and colimits
(Tag 03DB) and reflects isomorphisms, hence reflects them. `toSheafConstantIso` is `Iso.refl`,
which is Mathlib's `PresheafOfModules.sheafificationCompToSheaf` together with the fact that the
underlying abelian presheaf of the constant presheaf of modules on `M` is the constant presheaf
on `M`, an equality of functors that holds by `rfl`.

**Why `unitIsoConstantModuleSheaf` is proved by corepresentability.** The underlying abelian
sheaf of `SheafOfModules.unit R̲` is the sheafification of the constant presheaf of *rings*
composed with the forgetful functor to abelian groups, whereas the underlying abelian sheaf of
`R̲` as a constant sheaf of modules is the sheafification of the constant presheaf of abelian
groups. Comparing them directly would need the compatibility of sheafification with
`forget₂ RingCat AddCommGrpCat`, which the pinned Mathlib does not provide at an unrelated module
universe. The corepresentability argument avoids this entirely: the constant presheaf of modules
with value `R` *is* `PresheafOfModules.unit` of the constant presheaf of rings (by `rfl`), so the
sheafification adjunction gives `(R̲ ⟶ N) ≃ N.sections` naturally, which is the defining property
of `SheafOfModules.unit`.

**The hypotheses of part (2) are those of part (1).** Stacks proves (2) from (1) and Tag 082T,
which is the ringed-space case of Tag 01BP. The version of Tag 01BP in
`TensorExactnessSheafify.lean` assumes `HasBinaryProducts C`, `HasPullbacks C` and sheafification
on the twice iterated slice topologies, none of which Stacks requires of a site (Tag 00VH
deliberately avoids requiring fibre products). **None of the three is needed here**:

* `HasBinaryProducts C` entered only through the colimit preservation of restriction to a slice
  site, which is wanted by `SheafOfModules.Presentation.map` and `SheafOfModules.mapFreeIso`. For
  a *finite* presentation only finite coproducts are restricted, and restriction is an additive
  functor, so it preserves them unconditionally
  (`Stacks.SheafOfModules.SliceFinite.freeOverIso`).
* `HasPullbacks C` entered only through the restriction of a presentation along a morphism of the
  site, which is needed to refine the covering family on which the target is presented against
  the one on which the source is generated. Here the source is generated by finitely many
  *global* sections, so no refinement is needed and the presentation never moves
  (`Stacks.SheafOfModules.SliceFinite.isFiniteType_kernel_of_generatingSections`).
* The twice iterated slice hypotheses are not extra hypotheses at all: `((J.over U).over Z)` and
  `J.over Z.left` are equivalent sites via `CategoryTheory.Over.iteratedSliceEquiv`, so they
  follow from the once sliced ones
  (`Stacks.SheafOfModules.SliceFinite.hasSheafify_iteratedSlice`).

Part (2) is therefore faithful to the source, and the `@[stacks 093N "finite_presentation"]`
attribute sits on the equivalence in `StacksDraft.Ch18.Sec42.Tag093N`.

## References

* [Stacks Project, Tag 093N](https://stacks.math.columbia.edu/tag/093N)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DB](https://stacks.math.columbia.edu/tag/03DB)
* [Stacks Project, Tag 04B5](https://stacks.math.columbia.edu/tag/04B5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.SheafOfModules.Constant

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section LocallySurjective

/-- Finitely many sections of the target of a locally surjective morphism of abelian presheaves
have simultaneous representatives on a covering family none of whose members is sheaf
theoretically empty. -/
lemma exists_cover_representatives {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (φ : P ⟶ Q)
    [Presheaf.IsLocallySurjective J φ] (U : C) {r : ℕ} (s : Fin r → Q.obj (op U)) :
    ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧
        ∀ i, (¬ (⊥ : Sieve (V i)) ∈ J (V i)) ∧
          ∀ j, ∃ b : P.obj (op (V i)), Q.map (f i).op (s j) = φ.app (op (V i)) b := by
  classical
  let S₀ : Fin r → Sieve U := fun j => Presheaf.imageSieve φ (s j)
  have hS : Finset.univ.inf S₀ ∈ J U :=
    Stacks.Sheafification.finsetInf_covering J (U := U) (t := Finset.univ) (S := S₀)
      fun j => Presheaf.imageSieve_mem (J := J) (f := φ) (s := s j)
  let K : J.Cover U := ⟨Finset.univ.inf S₀, hS⟩
  let I : Type (max u v) := {a : K.Arrow // ¬ (⊥ : Sieve a.Y) ∈ J a.Y}
  let V : I → C := fun i => i.val.Y
  let f : ∀ i, V i ⟶ U := fun i => i.val.f
  have hT : Sieve.ofArrows V f ∈ J U := by
    refine J.transitive hS _ fun Y g hg => ?_
    by_cases hempty : (⊥ : Sieve Y) ∈ J Y
    · exact J.superset_covering bot_le hempty
    · have hTg : Sieve.ofArrows V f g := Sieve.ofArrows_mk V f ⟨⟨Y, g, hg⟩, hempty⟩
      exact J.superset_covering
        (by rw [Sieve.pullback_eq_top_of_mem (Sieve.ofArrows V f) hTg]) (J.top_mem Y)
  refine ⟨I, V, f, hT, fun i => ⟨i.property, fun j => ?_⟩⟩
  have hle : Finset.univ.inf S₀ ≤ S₀ j := Finset.inf_le (Finset.mem_univ j)
  have hjS : S₀ j (f i) := hle (Y := V i) (f i) i.val.hf
  obtain ⟨b, hb⟩ := hjS
  exact ⟨b, hb.symm⟩

end LocallySurjective

section Nonempty

/-- A covering sieve of an object which is not sheaf theoretically empty contains an arrow whose
source is not sheaf theoretically empty. -/
lemma exists_arrow_with_nonempty_source {U : C} (S : Sieve U)
    (hS : S ∈ J U) (hU : ¬ (⊥ : Sieve U) ∈ J U) :
    ∃ (V : C) (f : V ⟶ U), S f ∧ ¬ (⊥ : Sieve V) ∈ J V := by
  by_contra! h
  exact hU (J.transitive hS ⊥ h)

/-- If a family of objects covers the terminal object and some object is not sheaf theoretically
empty, then some member of the family is not sheaf theoretically empty. -/
lemma exists_nonempty_member_of_coversTop {I : Type*} (X : I → C)
    (hX : J.CoversTop X) (U : C) (hU : ¬ (⊥ : Sieve U) ∈ J U) :
    ∃ i, ¬ (⊥ : Sieve (X i)) ∈ J (X i) := by
  by_contra! h
  refine hU (J.transitive (hX U) ⊥ fun V f hf => ?_)
  obtain ⟨i, ⟨g⟩⟩ := (Sieve.mem_ofObjects_iff X f).mp hf
  simpa using J.pullback_stable g (h i)

/-- Over an object which is not sheaf theoretically empty, distinct elements of an abelian group
give distinct sections of the associated constant sheaf. -/
lemma constant_section_injective [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {A : Type w} [AddCommGroup A] (U : C) (hU : ¬ (⊥ : Sieve U) ∈ J U) :
    Function.Injective (fun a : A =>
      (toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of A))).app (op U) a) := by
  intro a b hab
  have hEq : Presheaf.equalizerSieve
      (F := (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of A)) (X := op U) a b ∈ J U :=
    Presheaf.equalizerSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of A))) (X := op U) a b hab
  obtain ⟨V, f, hf, hV⟩ := exists_arrow_with_nonempty_source J _ hEq hU
  have hlocal : ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of A)).map f.op a =
      ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of A)).map f.op b := by
    simpa only [Presheaf.equalizerSieve_apply] using hf
  simpa using hlocal

/-- The empty sieve of an object of a slice site covers it iff the empty sieve of its source
covers the source. -/
private lemma bot_mem_over_iff {U : C} (T : Over U) :
    (⊥ : Sieve T) ∈ (J.over U) T ↔ (⊥ : Sieve T.left) ∈ J T.left := by
  simp only [GrothendieckTopology.mem_over_iff, map_bot]

/-- The terminal object of a slice site over an object which is not sheaf theoretically empty is
not sheaf theoretically empty. -/
lemma nonempty_terminal_over {U : C} (hU : ¬ (⊥ : Sieve U) ∈ J U) :
    ¬ (⊥ : Sieve (Over.mk (𝟙 U))) ∈ (J.over U) (Over.mk (𝟙 U)) :=
  fun h => hU ((bot_mem_over_iff J _).mp h)

/-- A covering family of an object which is not sheaf theoretically empty is nonempty. -/
lemma nonempty_index_of_over_cover {U : C} {T : Over U} {I : Type*}
    (V : I → Over U) (f : ∀ i, V i ⟶ T)
    (hcover : Sieve.ofArrows V f ∈ (J.over U) T)
    (hT : ¬ (⊥ : Sieve T) ∈ (J.over U) T) : Nonempty I := by
  by_contra hI
  have : IsEmpty I := not_nonempty_iff.mp hI
  have hpre : Presieve.ofArrows V f = (⊥ : Presieve T) := by
    funext X g
    exact propext ⟨fun ⟨i⟩ => isEmptyElim i, fun h => by cases h⟩
  apply hT
  rw [← Sieve.generate_bot, ← hpre]
  exact hcover

end Nonempty

section Free

variable {R : Type w} [Ring R]

/-- An epimorphism of sheaves of modules is locally surjective on the underlying abelian
sheaves. -/
lemma epi_toSheaf_isLocallySurjective {S : Sheaf J RingCat.{w}}
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {F G : SheafOfModules.{w} S} (f : F ⟶ G) [Epi f] :
    Presheaf.IsLocallySurjective J ((SheafOfModules.toSheaf S).map f).hom := by
  have : HasSheafify J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have : PreservesColimitsOfSize.{0, 0} (SheafOfModules.toSheaf.{w} S) :=
    preservesSmallestColimits_of_preservesColimits _
  exact (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{w}
    ((SheafOfModules.toSheaf S).map f)).mpr inferInstance

/-- A point of a finite coproduct of copies of a presheaf of abelian groups is the sum of its
components. -/
private lemma presheaf_coproduct_point_decompose
    {I : Type w} [Fintype I] (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (X : Cᵒᵖ)
    (z : (∐ fun _ : I => P).obj X) :
    ∃ a : I → P.obj X, z = ∑ i, (Limits.Sigma.ι (fun _ : I => P) i).app X (a i) := by
  classical
  let K : Discrete I ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{w}) := Discrete.functor (fun _ : I => P)
  let E := (evaluation (Cᵒᵖ) AddCommGrpCat.{w}).obj X
  let D := fun i : I => (K ⋙ E).obj ⟨i⟩
  let _ : Limits.HasBiproduct D := Limits.HasBiproduct.of_hasCoproduct D
  let B := ⨁ D
  let e : E.obj (colimit K) ≅ colimit (K ⋙ E) := preservesColimitIso E K
  let kIso : K ⋙ E ≅ Discrete.functor D := Discrete.compNatIsoDiscrete _ E
  let e' : colimit (K ⋙ E) ≅ colimit (Discrete.functor D) := HasColimit.isoOfNatIso kIso
  let c : (∐ fun _ : I => P).obj X ≅ B :=
    e ≪≫ e' ≪≫ (Limits.biproduct.isoCoproduct D).symm
  let a (i : I) : P.obj X := (Limits.biproduct.π D i).hom (c.hom z)
  have htotal : (∑ i, Limits.biproduct.π D i ≫ Limits.biproduct.ι D i) = 𝟙 B :=
    Limits.IsBilimit.total (Limits.biproduct.isBilimit D)
  have hsumapp : ∀ (T : Finset I) (φ : I → (B ⟶ B)) (b : B),
      ConcreteCategory.hom (∑ i ∈ T, φ i) b = ∑ i ∈ T, ConcreteCategory.hom (φ i) b := by
    intro T φ b
    induction T using Finset.induction_on with
    | empty => rfl
    | @insert i T hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, AddCommGrpCat.hom_add_apply, ih]
  have hleg (i : I) :
      (Limits.Sigma.ι (fun _ : I => P) i).app X ≫ c.hom = Limits.biproduct.ι D i := by
    change E.map (colimit.ι K ⟨i⟩) ≫ e.hom ≫
      e'.hom ≫ (Limits.biproduct.isoCoproduct D).inv = Limits.biproduct.ι D i
    rw [← Category.assoc, ι_preservesColimitIso_hom]
    rw [← Category.assoc, HasColimit.ι_isoOfNatIso_hom kIso ⟨i⟩]
    simp only [Functor.comp_obj, Discrete.functor_obj_eq_as, biproduct.isoCoproduct_inv,
      Category.assoc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    exact Category.id_comp _
  refine ⟨a, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso c.hom).injective
  rw [map_sum]
  have hb : c.hom z = ∑ i, Limits.biproduct.ι D i (a i) := by
    have hb0 := congrArg (fun f : B ⟶ B => (ConcreteCategory.hom f) (c.hom z)) htotal.symm
    rw [hsumapp Finset.univ (fun i => Limits.biproduct.π D i ≫ Limits.biproduct.ι D i)
      (c.hom z)] at hb0
    simpa [AddCommGrpCat.comp_apply, a] using hb0
  rw [hb]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := congrArg (fun f => (ConcreteCategory.hom f) (a i)) (hleg i)
  simpa [AddCommGrpCat.comp_apply, a] using h.symm

/-- The canonical map from the presheaf coproduct of copies of the sheaf of rings to the
underlying presheaf of the free sheaf of modules is locally surjective. -/
private lemma free_underlying_presheaf_locally_surjective
    {S : Sheaf J RingCat.{w}}
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (I : Type w) :
    Presheaf.IsLocallySurjective J
      (show (∐ fun _ : I => (SheafOfModules.unit S).val.presheaf) ⟶
          (SheafOfModules.free (R := S) I).val.presheaf from
        Limits.Sigma.desc (fun i : I =>
          (PresheafOfModules.toPresheaf S.obj).map
            ((SheafOfModules.forget S).map (SheafOfModules.ιFree i)))) := by
  let L := PresheafOfModules.sheafification (R := S) (𝟙 S.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (R := S) (𝟙 S.obj)
  let G := (PresheafOfModules.toPresheaf S.obj).comp (presheafToSheaf J AddCommGrpCat.{w})
  have isoG : (L.comp (SheafOfModules.toSheaf S)) ≅ G :=
    PresheafOfModules.sheafificationCompToSheaf (R := S) (𝟙 S.obj)
  have : PreservesColimitsOfShape (Discrete I) L := inferInstance
  let K : Discrete I ⥤ PresheafOfModules.{w} S.obj :=
    Discrete.functor (fun _ : I => (SheafOfModules.unit S).val)
  have : HasColimitsOfShape (Discrete I) AddCommGrpCat.{w} := AddCommGrpCat.hasColimitsOfShape
  have : PreservesColimitsOfShape (Discrete I) (PresheafOfModules.toPresheaf S.obj) :=
    PresheafOfModules.toPresheaf_preservesColimitsOfShape S.obj (Discrete I)
  have : PreservesColimitsOfShape (Discrete I) (presheafToSheaf J AddCommGrpCat.{w}) :=
    (sheafificationAdjunction J AddCommGrpCat.{w}).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have : PreservesColimitsOfShape (Discrete I) G := Limits.comp_preservesColimitsOfShape _ _
  have : PreservesColimit K (L.comp (SheafOfModules.toSheaf S)) :=
    Limits.preservesColimit_of_natIso K isoG.symm
  have : IsIso adj.counit := inferInstance
  let e : Discrete.functor (fun _ : I => SheafOfModules.unit S) ≅ K.comp L :=
    Discrete.natIso (fun _ => (asIso (adj.counit.app (SheafOfModules.unit S))).symm ≪≫ Iso.refl _)
  have hc : IsColimit (L.mapCocone (colimit.cocone K)) :=
    isColimitOfPreserves L (colimit.isColimit K)
  have hF : IsColimit ((SheafOfModules.toSheaf S).mapCocone
      (L.mapCocone (colimit.cocone K))) :=
    isColimitOfPreserves (L.comp (SheafOfModules.toSheaf S)) (colimit.isColimit K)
  have hpc : PreservesColimit (K ⋙ L) (SheafOfModules.toSheaf S) :=
    preservesColimit_of_preserves_colimit_cocone hc hF
  have hpres : PreservesColimit
      (Discrete.functor (fun _ : I => SheafOfModules.unit S)) (SheafOfModules.toSheaf S) :=
    preservesColimit_of_iso_diagram (SheafOfModules.toSheaf S) e.symm
  let D : Discrete I ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{w}) :=
    Discrete.functor (fun _ : I => (SheafOfModules.unit S).val.presheaf)
  let Dq : Discrete I ⥤ Sheaf J AddCommGrpCat.{w} :=
    D.comp (presheafToSheaf J AddCommGrpCat.{w})
  let c : Cocone Dq := (presheafToSheaf J AddCommGrpCat.{w}).mapCocone (colimit.cocone D)
  have hcq : IsColimit c :=
    isColimitOfPreserves (presheafToSheaf J AddCommGrpCat.{w}) (colimit.isColimit D)
  let unitIso : (SheafOfModules.toSheaf S).obj (SheafOfModules.unit S) ≅
      (presheafToSheaf J AddCommGrpCat.{w}).obj (SheafOfModules.unit S).val.presheaf := by
    refine (sheafToPresheaf J AddCommGrpCat.{w}).preimageIso ?_
    exact isoSheafify J (SheafOfModules.unit S).isSheaf
  let diso : (Discrete.functor (fun _ : I => SheafOfModules.unit S)).comp
      (SheafOfModules.toSheaf S) ≅ Dq := Discrete.natIso (fun _ => unitIso)
  have hfree : IsColimit ((SheafOfModules.toSheaf S).mapCocone (SheafOfModules.freeCofan I)) :=
    isColimitOfPreserves (SheafOfModules.toSheaf S) (SheafOfModules.isColimitFreeCofan I)
  let β := hfree.coconePointsIsoOfNatIso hcq diso
  let m : (SheafOfModules.toSheaf S).obj (SheafOfModules.free I) ⟶
      (presheafToSheaf J AddCommGrpCat.{w}).obj (colimit D) := β.hom
  let η : (∐ fun _ : I => (SheafOfModules.unit S).val.presheaf) ⟶
      (SheafOfModules.free (R := S) I).val.presheaf :=
    Limits.Sigma.desc (fun i : I => (PresheafOfModules.toPresheaf S.obj).map
      ((SheafOfModules.forget S).map (SheafOfModules.ιFree i)))
  have hfac : η ≫ (sheafToPresheaf J AddCommGrpCat.{w}).map m = toSheafify J (colimit D) := by
    apply Limits.colimit.hom_ext
    intro i
    obtain ⟨i⟩ := i
    have hleg := hfree.comp_coconePointsIsoOfNatIso_hom hcq diso ⟨i⟩
    have hleg' := congrArg (fun f => (sheafToPresheaf J AddCommGrpCat.{w}).map f) hleg
    simp only [Functor.map_comp] at hleg'
    have hleg'' :
        (sheafToPresheaf J AddCommGrpCat.{w}).map
          (((SheafOfModules.toSheaf S).mapCocone (SheafOfModules.freeCofan I)).ι.app ⟨i⟩) ≫
            (sheafToPresheaf J AddCommGrpCat.{w}).map m =
        (sheafToPresheaf J AddCommGrpCat.{w}).map (diso.hom.app ⟨i⟩) ≫
          (sheafToPresheaf J AddCommGrpCat.{w}).map (c.ι.app ⟨i⟩) := hleg'
    have hηi : colimit.ι D ⟨i⟩ ≫ η =
        (sheafToPresheaf J AddCommGrpCat.{w}).map
          (((SheafOfModules.toSheaf S).mapCocone (SheafOfModules.freeCofan I)).ι.app ⟨i⟩) :=
      Sigma.ι_comp_desc _ i
    have hunit : (sheafToPresheaf J AddCommGrpCat.{w}).map unitIso.hom =
        toSheafify J (SheafOfModules.unit S).val.presheaf := by
      dsimp only [unitIso, Functor.preimageIso]
      rw [Functor.map_preimage]
      exact isoSheafify_hom J (SheafOfModules.unit S).isSheaf
    have hs : (sheafToPresheaf J AddCommGrpCat.{w}).map (c.ι.app ⟨i⟩) =
        sheafifyMap J (colimit.ι D ⟨i⟩) := rfl
    have hd : (sheafToPresheaf J AddCommGrpCat.{w}).map (diso.hom.app ⟨i⟩) =
        toSheafify J (SheafOfModules.unit S).val.presheaf := hunit
    have hfirst :
        colimit.ι D ⟨i⟩ ≫ η ≫ (sheafToPresheaf J AddCommGrpCat.{w}).map m =
        (sheafToPresheaf J AddCommGrpCat.{w}).map
          (((SheafOfModules.toSheaf S).mapCocone (SheafOfModules.freeCofan I)).ι.app ⟨i⟩) ≫
          (sheafToPresheaf J AddCommGrpCat.{w}).map m :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ (sheafToPresheaf J AddCommGrpCat.{w}).map m) hηi)
    exact hfirst.trans (hleg''.trans (by
      rw [hd, hs]
      exact (toSheafify_naturality _ _).symm))
  have : IsIso m := β.isIso_hom
  let mval := (sheafToPresheaf J AddCommGrpCat.{w}).map m
  have : IsIso mval := by
    dsimp [mval]
    infer_instance
  have hηloc : Presheaf.IsLocallySurjective J (toSheafify J (colimit D)) := inferInstance
  have hmloc : Presheaf.IsLocallyInjective J mval :=
    Presheaf.isLocallyInjective_of_injective J mval (fun X =>
      (ConcreteCategory.bijective_of_isIso (mval.app X)).injective)
  exact @Presheaf.isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective_fac
    _ _ J _ _ _ _ _ _ _ _ _ η ((sheafToPresheaf J AddCommGrpCat.{w}).map m)
    (toSheafify J (colimit D)) hfac hηloc hmloc

/-- If a composite out of a finite free sheaf of modules kills each basis section over every
object above `V`, then it is locally zero above `V`. -/
private lemma free_map_zero_locally
    {S : Sheaf J RingCat.{w}}
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {I : Type w} [Finite I] (F G : SheafOfModules.{w} S)
    (p : SheafOfModules.free (R := S) I ⟶ F) (q : F ⟶ G) (V : C)
    (hgen : ∀ (i : I) (W : C) (_g : W ⟶ V),
      (q.val.app (op W)).hom ((p.val.app (op W)).hom
        (((SheafOfModules.ιFree i).val.app (op W)).hom (1 : S.obj.obj (op W)))) = 0)
    {U : C} (f : U ⟶ V) (x : (SheafOfModules.free (R := S) I).val.presheaf.obj (op U)) :
    ∃ T : Sieve U, T ∈ J U ∧ ∀ (W : C) (g : W ⟶ U), T g →
      (((PresheafOfModules.toPresheaf S.obj).map
        ((SheafOfModules.forget S).map (p ≫ q))).app (op W))
        ((SheafOfModules.free (R := S) I).val.presheaf.map g.op x) = 0 := by
  classical
  let _ := Fintype.ofFinite I
  let η : (∐ fun _ : I => (SheafOfModules.unit S).val.presheaf) ⟶
      (SheafOfModules.free (R := S) I).val.presheaf :=
    Limits.Sigma.desc (fun i : I => (PresheafOfModules.toPresheaf S.obj).map
      ((SheafOfModules.forget S).map (SheafOfModules.ιFree i)))
  let β : (SheafOfModules.free (R := S) I).val.presheaf ⟶ G.val.presheaf :=
    (PresheafOfModules.toPresheaf S.obj).map ((SheafOfModules.forget S).map (p ≫ q))
  have hη : Presheaf.IsLocallySurjective J η := free_underlying_presheaf_locally_surjective J I
  refine ⟨Presheaf.imageSieve η x, Presheaf.imageSieve_mem J η x, ?_⟩
  intro W g hg
  obtain ⟨z, hz⟩ := hg
  obtain ⟨a, ha⟩ := presheaf_coproduct_point_decompose
    ((SheafOfModules.unit S).val.presheaf) (op W) z
  change (β.app (op W)) ((SheafOfModules.free (R := S) I).val.presheaf.map g.op x) = 0
  rw [← hz, ha, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hηi : Limits.Sigma.ι (fun _ : I => (SheafOfModules.unit S).val.presheaf) i ≫ η =
      (PresheafOfModules.toPresheaf S.obj).map
        ((SheafOfModules.forget S).map (SheafOfModules.ιFree (R := S) i)) :=
    Sigma.ι_comp_desc _ i
  have hval := congrArg (fun k => (k.app (op W)) (a i)) hηi
  simp only [NatTrans.comp_app] at hval
  rw [AddCommGrpCat.comp_apply] at hval
  have hterm : (β.app (op W))
      (η.app (op W) ((Limits.Sigma.ι (fun _ : I =>
        (SheafOfModules.unit S).val.presheaf) i).app (op W) (a i))) = 0 := by
    rw [hval]
    have hterm' : (q.val.app (op W)).hom ((p.val.app (op W)).hom
        (((SheafOfModules.ιFree (R := S) i).val.app (op W)).hom (a i))) = 0 := by
      have h1 : ((SheafOfModules.ιFree (R := S) i).val.app (op W)).hom (a i) =
          (show S.obj.obj (op W) from a i) •
            ((SheafOfModules.ιFree (R := S) i).val.app (op W)).hom
              (1 : S.obj.obj (op W)) := by
        refine Eq.trans ?_
          (map_smul _ (show S.obj.obj (op W) from a i) (1 : S.obj.obj (op W)))
        congr 1
        change (show S.obj.obj (op W) from a i) =
          (show S.obj.obj (op W) from a i) * 1
        exact (mul_one _).symm
      rw [h1, map_smul, map_smul, hgen i W (g ≫ f), smul_zero]
    convert hterm' using 1 <;> rfl
  simpa [hterm]

end Free

section Definition

variable {R : Type w} [Ring R]

/-- The constant presheaf of `R`-modules attached to an `R`-module, as a presheaf of modules
over the constant presheaf of rings with value `R`. -/
noncomputable abbrev constantModulePresheaf (M : ModuleCat.{w} R) :
    PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of R)) :=
  (PresheafOfModules.constFunctor
    (CategoryTheory.Limits.constCocone Cᵒᵖ (RingCat.of R))).obj M

variable [HasWeakSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The constant sheaf of modules with value `M`, regarded as a sheaf of modules over the
constant sheaf of rings with value `R`. -/
noncomputable abbrev constantModuleSheaf (M : ModuleCat.{w} R) :
    SheafOfModules.{w} ((constantSheaf J RingCat.{w}).obj (RingCat.of R)) :=
  (PresheafOfModules.sheafification
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).obj (constantModulePresheaf M)

/-- The morphism of constant sheaves of modules attached to a morphism of modules. -/
noncomputable def constantModuleSheafMap {M N : ModuleCat.{w} R} (f : M ⟶ N) :
    constantModuleSheaf J M ⟶ constantModuleSheaf J N :=
  (PresheafOfModules.sheafification
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).map
      ((PresheafOfModules.constFunctor
        (CategoryTheory.Limits.constCocone Cᵒᵖ (RingCat.of R))).map f)

/-- The global section of the restriction of `constantModuleSheaf J M` to the slice site over
`U` determined by an element of `M`. -/
noncomputable def constantSectionOver (M : ModuleCat.{w} R) (U : C) (m : M) :
    ((constantModuleSheaf J M).over U).sections := by
  let α := toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))
  let P := constantModulePresheaf (C := C) (R := R) M
  let η := (PresheafOfModules.sheafificationAdjunction α).unit.app P
  let s₀ := P.sectionsMk (fun _ => m) (by
    intro X Y f
    simp [P]
    rfl)
  let s := PresheafOfModules.sectionsMap η s₀
  refine ((constantModuleSheaf J M).over U).val.sectionsMk (fun V => s.1 (op V.unop.left)) ?_
  exact fun V W f => PresheafOfModules.sections_property s f.unop.left.op

/-- The value over `U` of the section of `constantModuleSheaf J M` determined by `m`. -/
noncomputable abbrev constantValue (M : ModuleCat.{w} R) (U : C) (m : M) :
    (constantModuleSheaf J M).val.obj (op U) :=
  (toSheafify J (constantModulePresheaf (C := C) M).presheaf).app (op U) m

/-- The section `constantSectionOver J M U m` takes the value `constantValue J M V.left m` over
each `V : Over U`. -/
lemma constantSectionOver_value (M : ModuleCat.{w} R) (U : C) (m : M) (V : Over U) :
    (constantSectionOver J M U m).val (op V) = constantValue J M V.left m := by
  let α := toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))
  let P := constantModulePresheaf (C := C) (R := R) M
  let η := (PresheafOfModules.sheafificationAdjunction α).unit.app P
  change ((PresheafOfModules.toPresheaf ((Functor.const Cᵒᵖ).obj (RingCat.of R))).map η).app
      (op V.left) m = _
  have h := PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app α P
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op V.left)) m

/-- The map of constant sheaves of modules induced by `f : M ⟶ N` sends the section over `U`
determined by `m` to the section determined by `f m`. -/
lemma constantModuleSheafMap_constantSectionOver {M N : ModuleCat.{w} R} (f : M ⟶ N) (U : C)
    (m : M) :
    SheafOfModules.sectionsMap ((constantModuleSheafMap J f).over U)
      (constantSectionOver J M U m) = constantSectionOver J N U (f.hom m) := by
  let α := toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))
  let adj := PresheafOfModules.sheafificationAdjunction α
  let P := constantModulePresheaf (C := C) (R := R) M
  let Q := constantModulePresheaf (C := C) (R := R) N
  let f₀ := (PresheafOfModules.constFunctor
    (CategoryTheory.Limits.constCocone Cᵒᵖ (RingCat.of R))).map f
  have hn := NatTrans.naturality adj.unit f₀
  apply PresheafOfModules.sections_ext
  intro V
  have hnV := congrArg (fun g => g.app (op V.unop.left)) hn
  have hnVm := ConcreteCategory.congr_hom hnV m
  change (ConcreteCategory.hom
      ((adj.unit.app P ≫ (PresheafOfModules.sheafification α ⋙
        SheafOfModules.forget ((presheafToSheaf J RingCat).obj
          ((Functor.const Cᵒᵖ).obj (RingCat.of R))) ⋙
        PresheafOfModules.restrictScalars α).map f₀).app (op V.unop.left))) m =
    (ConcreteCategory.hom
      (((𝟭 (PresheafOfModules ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).map f₀ ≫
        adj.unit.app Q).app (op V.unop.left))) m
  exact hnVm.symm

/-- Restriction along `f : V ⟶ U` sends the constant value of `m` over `U` to the constant value
of `m` over `V`. -/
lemma constantValue_map (M : ModuleCat.{w} R) {U V : C} (f : V ⟶ U) (m : M) :
    (constantModuleSheaf J M).val.presheaf.map f.op (constantValue J M U m) =
      constantValue J M V m :=
  (NatTrans.naturality_apply
    (toSheafify J (constantModulePresheaf (C := C) M).presheaf) f.op m).symm

/-- The map of constant sheaves of modules induced by `f : M ⟶ N` sends the constant value of `m`
over `U` to the constant value of `f m`. -/
lemma constantValue_map_hom {M N : ModuleCat.{w} R} (f : M ⟶ N) (U : C) (m : M) :
    (constantModuleSheafMap J f).val.app (op U) (constantValue J M U m) =
      constantValue J N U (f.hom m) := by
  have h := congrArg (fun s => s.val (op (Over.mk (𝟙 U))))
    (constantModuleSheafMap_constantSectionOver J f U m)
  change (constantModuleSheafMap J f).val.app (op U)
      ((constantSectionOver J M U m).val (op (Over.mk (𝟙 U)))) =
    (constantSectionOver J N U (f.hom m)).val (op (Over.mk (𝟙 U))) at h
  rw [constantSectionOver_value, constantSectionOver_value] at h
  exact h

/-- In the sheafification of the constant presheaf of modules, the image of `a` acts on the image
of `m` as the image of `a • m`. -/
lemma constantModuleSheaf_smul_constant (M : ModuleCat.{w} R) (U : C)
    (a : ((Functor.const Cᵒᵖ).obj (RingCat.of R)).obj (op U))
    (m : (constantModulePresheaf (C := C) (R := R) M).obj (op U)) :
    PresheafOfModules.Sheafify.smul
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))
      (toSheafify J (constantModulePresheaf (C := C) (R := R) M).presheaf)
      (((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app (op U)) a)
      (((toSheafify J (constantModulePresheaf (C := C) (R := R) M).presheaf).app (op U)) m) =
    (toSheafify J (constantModulePresheaf (C := C) (R := R) M).presheaf).app (op U) (a • m) := by
  let α := toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))
  let P := constantModulePresheaf (C := C) (R := R) M
  let φ := toSheafify J P.presheaf
  change PresheafOfModules.Sheafify.smul α φ (α.app (op U) a) (φ.app (op U) m) =
    φ.app (op U) (a • m)
  simpa using PresheafOfModules.Sheafify.map_smul_eq α φ (α.app (op U) a) (φ.app (op U) m)
    (𝟙 (op U)) a (by simp) m (by simp)

/-- The constant value of `a • m` over `U` is the constant section `a` of the constant sheaf of
rings acting on the constant value of `m`. -/
lemma constantValue_smul (M : ModuleCat.{w} R) (U : C) (a : R) (m : M) :
    constantValue J M U (a • m) =
      (show ((constantSheaf J RingCat).obj (RingCat.of R)).obj.obj (op U) from
        (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app (op U) a) •
        constantValue J M U m :=
  (constantModuleSheaf_smul_constant J M U a m).symm

end Definition

section FiniteType

variable {R : Type w} [Ring R]

private lemma module_finite_of_span_range_eq_top
    {I : Type*} [Finite I] {M : Type w} [AddCommGroup M] [Module R M]
    (s : I → M) (hspan : Submodule.span R (Set.range s) = ⊤) : Module.Finite R M :=
  Module.Finite.of_fg_top <| Submodule.fg_def.mpr ⟨Set.range s, Set.finite_range s, hspan⟩

/-- The value over `U` of the global section of a sheaf of modules corresponding to the `i`-th
basis vector under `SheafOfModules.freeHomEquiv`. -/
lemma freeHomEquiv_value {S : Sheaf J RingCat.{w}}
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (F : SheafOfModules.{w} S) {I : Type w} (p : SheafOfModules.free I ⟶ F) (i : I) (U : C) :
    p.val.app (op U) ((SheafOfModules.ιFree i).val.app (op U) (1 : S.obj.obj (op U))) =
      (F.freeHomEquiv p i).val (op U) := rfl

variable [HasWeakSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Finitely many sections of `constantModuleSheaf J M` over `U` are simultaneously constant on
a covering family of `U` none of whose members is sheaf theoretically empty. -/
lemma exists_cover_constantModule_representatives (M : ModuleCat.{w} R) (U : C) {r : ℕ}
    (s : Fin r → (constantModuleSheaf J M).val.presheaf.obj (op U)) :
    ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧
        ∀ i, (¬ (⊥ : Sieve (V i)) ∈ J (V i)) ∧
          ∀ j, ∃ m : M,
            (constantModuleSheaf J M).val.presheaf.map (f i).op (s j) =
              (toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of M))).app (op (V i)) m := by
  obtain ⟨I, V, f, hcover, h⟩ := exists_cover_representatives J
    (toSheafify J (constantModulePresheaf (C := C) (R := R) M).presheaf) U s
  exact ⟨I, V, f, hcover, h⟩

/-- The slice version of `exists_cover_constantModule_representatives`. -/
lemma exists_cover_constantModule_representatives_over (M : ModuleCat.{w} R) (U : C) (T : Over U)
    {r : ℕ} (s : Fin r → ((constantModuleSheaf J M).over U).val.presheaf.obj (op T)) :
    ∃ (I : Type (max u v)) (V : I → Over U) (f : ∀ i, V i ⟶ T),
      Sieve.ofArrows V f ∈ (J.over U) T ∧
        ∀ i, (¬ (⊥ : Sieve (V i).left) ∈ J (V i).left) ∧ ∀ j, ∃ m : M,
            (((constantModuleSheaf J M).over U).val.presheaf.map (f i).op (s j)) =
              (toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of M))).app
                (op (V i).left) m := by
  obtain ⟨I, V₀, f₀, hcover, hrep⟩ :=
    exists_cover_constantModule_representatives J M T.left s
  let V (i : I) : Over U := Over.mk (f₀ i ≫ T.hom)
  let f (i : I) : V i ⟶ T := Over.homMk (f₀ i)
  refine ⟨I, V, f, ?_, ?_⟩
  · rw [GrothendieckTopology.mem_over_iff]
    simpa [V, f, Sieve.overEquiv_ofArrows] using hcover
  · intro i
    refine ⟨(hrep i).1, ?_⟩
    intro j
    obtain ⟨m, hm⟩ := (hrep i).2 j
    refine ⟨m, ?_⟩
    change (constantModuleSheaf J M).val.presheaf.map (f₀ i).op (s j) = _
    exact hm

/-- If the restriction of `constantModuleSheaf J M` to a slice site over a non sheaf
theoretically empty object `U` is generated by finitely many sections, then `M` is a finite
`R`-module. -/
lemma finite_of_generatingSections (M : ModuleCat.{w} R) (U : C)
    [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (hU : ¬ (⊥ : Sieve U) ∈ J U)
    (σ : ((constantModuleSheaf J M).over U).GeneratingSections) [σ.IsFiniteType] :
    Module.Finite R M := by
  classical
  let _ := Fintype.ofFinite σ.I
  let e := (Fintype.equivFin σ.I).symm
  let T : Over U := Over.mk (𝟙 U)
  obtain ⟨K, V, f, hcover, hrep⟩ :=
    exists_cover_constantModule_representatives_over J M U T
      (fun j => (σ.s (e j)).val (op T))
  have : Nonempty K :=
    nonempty_index_of_over_cover J V f hcover (nonempty_terminal_over J hU)
  let k : K := Classical.choice this
  let V₀ := V k
  have hV₀ : ¬ (⊥ : Sieve V₀) ∈ (J.over U) V₀ := (bot_mem_over_iff J V₀).not.mpr (hrep k).1
  choose m hm using (hrep k).2
  let x : σ.I → M := fun i => m (e.symm i)
  have hs (i : σ.I) : (σ.s i).val (op V₀) = constantValue J M V₀.left (x i) := by
    have h := hm (e.symm i)
    have h' := (PresheafOfModules.sections_property (σ.s (e (e.symm i))) (f k).op).symm.trans h
    simp only [e.apply_symm_apply] at h'
    exact h'
  let N : Submodule R M := Submodule.span R (Set.range x)
  let Q : ModuleCat.{w} R := ModuleCat.of R (M ⧸ N)
  let q₀ : M ⟶ Q := ModuleCat.ofHom N.mkQ
  let F := (constantModuleSheaf J M).over U
  let G := (constantModuleSheaf J Q).over U
  let p := σ.π
  let q : F ⟶ G := (constantModuleSheafMap J q₀).over U
  have hgen (i : σ.I) (W : Over U) (g : W ⟶ V₀) :
      (q.val.app (op W)).hom ((p.val.app (op W)).hom
        (((SheafOfModules.ιFree i).val.app (op W)).hom
          (1 : (((constantSheaf J RingCat).obj (RingCat.of R)).over U).obj.obj (op W)))) = 0 := by
    have hsi : (σ.s i).val (op W) = constantValue J M W.left (x i) := by
      rw [← PresheafOfModules.sections_property (σ.s i) g.op, hs]
      exact constantValue_map J M g.left (x i)
    change q.val.app (op W) (p.val.app (op W)
      ((SheafOfModules.ιFree i).val.app (op W)
        (1 : (((constantSheaf J RingCat).obj (RingCat.of R)).over U).obj.obj (op W)))) = 0
    rw [freeHomEquiv_value (J.over U) F p, Equiv.apply_symm_apply, hsi]
    change (constantModuleSheafMap J q₀).val.app (op W.left)
      (constantValue J M W.left (x i)) = 0
    rw [constantValue_map_hom]
    have hx : q₀.hom (x i) = 0 :=
      (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨i, rfl⟩)
    rw [hx]
    exact map_zero _
  have hp : Presheaf.IsLocallySurjective (J.over U) ((SheafOfModules.toSheaf _).map p).hom :=
    epi_toSheaf_isLocallySurjective (J.over U) p
  have htop : N = ⊤ := by
    refine top_unique fun a _ => ?_
    let av : F.val.presheaf.obj (op V₀) := constantValue J M V₀.left a
    obtain ⟨W, g, ⟨y, hy⟩, hW⟩ := exists_arrow_with_nonempty_source (J.over U)
      (Presheaf.imageSieve ((SheafOfModules.toSheaf _).map p).hom av)
      (Presheaf.imageSieve_mem (J.over U) ((SheafOfModules.toSheaf _).map p).hom av) hV₀
    obtain ⟨Sv, hSv, hz⟩ := free_map_zero_locally (J.over U) F G p q V₀ hgen g y
    obtain ⟨Z, t, ht, hZ⟩ := exists_arrow_with_nonempty_source (J.over U) Sv hSv hW
    have hzero := hz Z t ht
    have hpy : p.val.app (op W) y = constantValue J M W.left a :=
      hy.trans (constantValue_map J M g.left a)
    have hpz : p.val.app (op Z)
        ((SheafOfModules.free σ.I).val.presheaf.map t.op y) =
        constantValue J M Z.left a :=
      (NatTrans.naturality_apply ((SheafOfModules.toSheaf _).map p).hom t.op y).trans
        ((congrArg (F.val.presheaf.map t.op) hpy).trans (constantValue_map J M t.left a))
    change q.val.app (op Z) (p.val.app (op Z)
      ((SheafOfModules.free σ.I).val.presheaf.map t.op y)) = 0 at hzero
    rw [hpz] at hzero
    change (constantModuleSheafMap J q₀).val.app (op Z.left)
      (constantValue J M Z.left a) = 0 at hzero
    rw [constantValue_map_hom] at hzero
    have ha : q₀.hom a = 0 :=
      constant_section_injective J Z.left ((bot_mem_over_iff J Z).not.mp hZ)
        (hzero.trans (map_zero _).symm)
    exact (Submodule.Quotient.mk_eq_zero N).mp ha
  exact module_finite_of_span_range_eq_top x htop

/-- A family of elements of `M` spanning `M` gives an epimorphism from a free sheaf of modules
onto the restriction of `constantModuleSheaf J M` to the slice site over `U`. -/
lemma constant_generators_epi (M : ModuleCat.{w} R) (U : C)
    [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {I : Type w} (x : I → M) (hx : Submodule.span R (Set.range x) = ⊤) :
    Epi (((constantModuleSheaf J M).over U).freeHomEquiv.symm
      (fun i => constantSectionOver J M U (x i))) := by
  let F := (constantModuleSheaf J M).over U
  let p := F.freeHomEquiv.symm (fun i => constantSectionOver J M U (x i))
  have hconstant (V : Over U) (m : M) :
      ∃ y, p.val.app (op V) y = constantValue J M V.left m := by
    have hm : m ∈ Submodule.span R (Set.range x) := by simp [hx]
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨i, rfl⟩ := hm
      refine ⟨(SheafOfModules.ιFree i).val.app (op V)
        (1 : (((constantSheaf J RingCat).obj (RingCat.of R)).over U).obj.obj (op V)), ?_⟩
      rw [freeHomEquiv_value (J.over U) F p, Equiv.apply_symm_apply]
      exact constantSectionOver_value J M U (x i) V
    | zero => exact ⟨0, by exact (map_zero _).trans (map_zero _).symm⟩
    | add a b _ _ ia ib =>
      obtain ⟨a', ha'⟩ := ia
      obtain ⟨b', hb'⟩ := ib
      refine ⟨a' + b', ?_⟩
      rw [map_add, ha', hb']
      exact (map_add _ _ _).symm
    | smul a b _ ih =>
      obtain ⟨b', hb'⟩ := ih
      refine ⟨(show (((constantSheaf J RingCat).obj (RingCat.of R)).over U).obj.obj (op V) from
          (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app (op V.left) a) • b', ?_⟩
      rw [map_smul, hb', constantValue_smul]
      rfl
  have hp : Presheaf.IsLocallySurjective (J.over U)
      ((SheafOfModules.toSheaf _).map p).hom := by
    constructor
    intro V y
    obtain ⟨K, W, f, hcover, hrep⟩ :=
      exists_cover_constantModule_representatives_over J M U V (fun _ : Fin 1 => y)
    apply (J.over U).superset_covering ((Sieve.generate_le_iff _ _).mpr ?_) hcover
    intro Z g hg
    cases hg with
    | mk k =>
      obtain ⟨mk, hmk⟩ := (hrep k).2 0
      obtain ⟨z, hz⟩ := hconstant (W k) mk
      exact ⟨z, hz.trans hmk.symm⟩
  exact (SheafOfModules.toSheaf _).epi_of_epi_map
    (Sheaf.epi_of_isLocallySurjective ((SheafOfModules.toSheaf _).map p))

/-- The constant sheaf of modules on a finite module is of finite type. -/
lemma isFiniteType_of_finite (M : ModuleCat.{w} R)
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [Module.Finite R M] : SheafOfModules.IsFiniteType (constantModuleSheaf J M) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  have hx : Submodule.span R (Set.range (fun i : s => (i : M))) = ⊤ := by
    rwa [show Set.range (fun i : s => (i : M)) = (s : Set M) by ext; simp]
  let σ : (constantModuleSheaf J M).LocalGeneratorsData :=
    { I := C
      X := id
      coversTop := fun U => J.covering_of_eq_top (by simp)
      generators := fun U =>
        { I := s
          s := fun i => constantSectionOver J M U i
          epi := constant_generators_epi J M U (fun i : s => (i : M)) hx } }
  exact ⟨⟨σ, ⟨fun _ => ⟨inferInstanceAs (Finite s)⟩⟩⟩⟩

/-- **Stacks Project, Tag 093N, part (1).** On a site whose topos is not empty, a constant sheaf
of modules is of finite type if and only if its value is a finitely generated module. -/
@[stacks 093N "finite_type"]
theorem constantModuleSheaf_isFiniteType_iff
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (hJ : ∃ U : C, ¬ (⊥ : Sieve U) ∈ J U) (M : ModuleCat.{w} R) :
    SheafOfModules.IsFiniteType (constantModuleSheaf J M) ↔ ModuleCat.isFG R M := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ :=
      SheafOfModules.IsFiniteType.exists_localGeneratorsData (constantModuleSheaf J M)
    obtain ⟨U, hU⟩ := hJ
    obtain ⟨i, hi⟩ := exists_nonempty_member_of_coversTop J σ.X σ.coversTop U hU
    have := hσ.isFiniteType i
    exact finite_of_generatingSections J M (σ.X i) hi (σ.generators i)
  · intro h
    have : Module.Finite R M := h
    exact isFiniteType_of_finite J M

end FiniteType

section Exactness

variable {R : Type w} [Ring R]

/-- The forgetful functor from sheaves of modules to abelian sheaves reflects isomorphisms: it
is faithful, hence reflects monomorphisms and epimorphisms, and the category of sheaves of
modules is abelian. -/
lemma reflectsIsomorphisms_toSheaf {S : Sheaf J RingCat.{w}}
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    (SheafOfModules.toSheaf.{w} S).ReflectsIsomorphisms where
  reflects {F G} f hf := by
    have h1 : Mono ((SheafOfModules.toSheaf S).map f) := inferInstance
    have h2 : Epi ((SheafOfModules.toSheaf S).map f) := inferInstance
    have : Mono f := Functor.ReflectsMonomorphisms.reflects f h1
    have : Epi f := Functor.ReflectsEpimorphisms.reflects f h2
    exact isIso_of_mono_of_epi f

variable [HasWeakSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The sheafification functor from presheaves of modules over the constant presheaf of rings
to sheaves of modules over the constant sheaf of rings. -/
noncomputable def moduleSheafification :=
  PresheafOfModules.sheafification.{w}
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))

/-- The constant sheaf of modules functor `ModuleCat R ⥤ SheafOfModules R̲`. -/
noncomputable def constantModuleSheafFunctor :=
  PresheafOfModules.constFunctor.{w}
      (CategoryTheory.Limits.constCocone Cᵒᵖ (RingCat.of R)) ⋙
    moduleSheafification J (R := R)

/-- The constant sheaf of modules functor sends `M` to `constantModuleSheaf J M`. -/
lemma constantModuleSheafFunctor_obj (M : ModuleCat.{w} R) :
    (constantModuleSheafFunctor J (R := R)).obj M = constantModuleSheaf J M := rfl

/-- The constant sheaf of modules functor sends `f` to `constantModuleSheafMap J f`. -/
lemma constantModuleSheafFunctor_map {M N : ModuleCat.{w} R} (f : M ⟶ N) :
    (constantModuleSheafFunctor J (R := R)).map f = constantModuleSheafMap J f := rfl

/-- The underlying abelian sheaf of a constant sheaf of modules is the constant abelian sheaf
on the underlying abelian group. -/
noncomputable def toSheafConstantIso :
    constantModuleSheafFunctor J (R := R) ⋙
        SheafOfModules.toSheaf ((constantSheaf J RingCat.{w}).obj (RingCat.of R)) ≅
      forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w} ⋙ constantSheaf J AddCommGrpCat.{w} :=
  Iso.refl _

/-- The constant sheaf of modules functor preserves finite limits. -/
instance preservesFiniteLimits_constantModuleSheafFunctor :
    PreservesFiniteLimits (constantModuleSheafFunctor J (R := R)) where
  preservesFiniteLimits K _ _ := by
    have hsf : HasSheafify J AddCommGrpCat.{w} :=
      AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
    have hcst : PreservesLimitsOfShape K (constantSheaf J AddCommGrpCat.{w}) :=
      inferInstanceAs (PreservesLimitsOfShape K
        (Functor.const Cᵒᵖ ⋙ presheafToSheaf J AddCommGrpCat.{w}))
    have hc : PreservesLimitsOfShape K
        (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w} ⋙ constantSheaf J AddCommGrpCat.{w}) :=
      comp_preservesLimitsOfShape (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})
        (constantSheaf J AddCommGrpCat.{w})
    have h1 : PreservesLimitsOfShape K (constantModuleSheafFunctor J (R := R) ⋙
        SheafOfModules.toSheaf.{w} ((constantSheaf J RingCat.{w}).obj (RingCat.of R))) :=
      (preservesLimitsOfShape_iff_of_natIso (toSheafConstantIso J)).mpr hc
    have h0 : PreservesLimitsOfSize.{0, 0}
        (SheafOfModules.toSheaf.{w} ((constantSheaf J RingCat.{w}).obj (RingCat.of R))) :=
      preservesSmallestLimits_of_preservesLimits _
    have hp : PreservesLimitsOfShape K
        (SheafOfModules.toSheaf.{w} ((constantSheaf J RingCat.{w}).obj (RingCat.of R))) :=
      h0.preservesLimitsOfShape
    have h2 : ReflectsLimitsOfShape K
        (SheafOfModules.toSheaf.{w} ((constantSheaf J RingCat.{w}).obj (RingCat.of R))) := by
      apply reflectsLimitsOfShape_of_reflectsIsomorphisms
    exact @preservesLimitsOfShape_of_reflects_of_preserves _ _ _ _ _ _ _ _
      (constantModuleSheafFunctor J (R := R))
      (SheafOfModules.toSheaf.{w} ((constantSheaf J RingCat.{w}).obj (RingCat.of R))) h1 h2

/-- The constant sheaf of modules functor preserves finite colimits. -/
instance preservesFiniteColimits_constantModuleSheafFunctor :
    PreservesFiniteColimits (constantModuleSheafFunctor J (R := R)) where
  preservesFiniteColimits K _ _ := by
    have hsf : HasSheafify J AddCommGrpCat.{w} :=
      AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
    have hcst : PreservesColimitsOfShape K (constantSheaf J AddCommGrpCat.{w}) :=
      inferInstanceAs (PreservesColimitsOfShape K
        (Functor.const Cᵒᵖ ⋙ presheafToSheaf J AddCommGrpCat.{w}))
    have hc : PreservesColimitsOfShape K
        (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w} ⋙ constantSheaf J AddCommGrpCat.{w}) :=
      comp_preservesColimitsOfShape (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})
        (constantSheaf J AddCommGrpCat.{w})
    have h1 : PreservesColimitsOfShape K (constantModuleSheafFunctor J (R := R) ⋙
        SheafOfModules.toSheaf.{w} ((constantSheaf J RingCat.{w}).obj (RingCat.of R))) :=
      (preservesColimitsOfShape_iff_of_natIso (toSheafConstantIso J)).mpr hc
    have h0 : PreservesColimitsOfSize.{0, 0}
        (SheafOfModules.toSheaf.{w} ((constantSheaf J RingCat.{w}).obj (RingCat.of R))) :=
      preservesSmallestColimits_of_preservesColimits _
    have hp : PreservesColimitsOfShape K
        (SheafOfModules.toSheaf.{w} ((constantSheaf J RingCat.{w}).obj (RingCat.of R))) :=
      h0.preservesColimitsOfShape
    have h2 : ReflectsColimitsOfShape K
        (SheafOfModules.toSheaf.{w} ((constantSheaf J RingCat.{w}).obj (RingCat.of R))) := by
      apply reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact @preservesColimitsOfShape_of_reflects_of_preserves _ _ _ _ _ _ _ _
      (constantModuleSheafFunctor J (R := R))
      (SheafOfModules.toSheaf.{w} ((constantSheaf J RingCat.{w}).obj (RingCat.of R))) h1 h2

end Exactness

section Unit

variable {R : Type w} [Ring R]
variable [HasWeakSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Just like `SheafOfModules.unit`, the constant sheaf of modules on the ring itself
corepresents global sections: morphisms out of it into `M` are the same as global sections
of `M`. This is the sheafification adjunction composed with
`PresheafOfModules.unitHomEquiv`, available because the constant presheaf of modules with
value `R` *is* the unit presheaf of modules over the constant presheaf of rings. -/
noncomputable def constantUnitHomEquiv
    (M : SheafOfModules.{w} ((constantSheaf J RingCat.{w}).obj (RingCat.of R))) :
    (constantModuleSheaf J (ModuleCat.of R R) ⟶ M) ≃ M.sections :=
  (PresheafOfModules.sheafificationHomEquiv
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).trans
      (PresheafOfModules.unitHomEquiv _)

/-- The bijection `constantUnitHomEquiv` is natural in the target: composing with `p : M ⟶ N`
corresponds to mapping global sections along `p`. -/
lemma constantUnitHomEquiv_comp
    {M N : SheafOfModules.{w} ((constantSheaf J RingCat.{w}).obj (RingCat.of R))}
    (h : constantModuleSheaf J (ModuleCat.of R R) ⟶ M) (p : M ⟶ N) :
    constantUnitHomEquiv J N (h ≫ p) =
      SheafOfModules.sectionsMap p (constantUnitHomEquiv J M h) := by
  have hadj : PresheafOfModules.sheafificationHomEquiv
        (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))) (h ≫ p) =
      PresheafOfModules.sheafificationHomEquiv
        (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))) h ≫
        (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).map p :=
    (PresheafOfModules.sheafificationAdjunction
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).homEquiv_naturality_right h p
  change PresheafOfModules.unitHomEquiv _ (PresheafOfModules.sheafificationHomEquiv
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))) (h ≫ p)) = _
  exact congrArg (PresheafOfModules.unitHomEquiv _) hadj

/-- The unit sheaf of modules is the constant sheaf of modules with value `R`: both
corepresent the global sections functor. -/
noncomputable def unitIsoConstantModuleSheaf :
    SheafOfModules.unit ((constantSheaf J RingCat.{w}).obj (RingCat.of R)) ≅
      constantModuleSheaf J (ModuleCat.of R R) where
  hom := (SheafOfModules.unitHomEquiv _).symm
    (constantUnitHomEquiv J _ (𝟙 (constantModuleSheaf J (ModuleCat.of R R))))
  inv := (constantUnitHomEquiv J _).symm
    ((SheafOfModules.unitHomEquiv _) (𝟙 (SheafOfModules.unit _)))
  hom_inv_id := by
    apply (SheafOfModules.unitHomEquiv _).injective
    have h := constantUnitHomEquiv_comp J (𝟙 (constantModuleSheaf J (ModuleCat.of R R)))
      ((constantUnitHomEquiv J _).symm
        ((SheafOfModules.unitHomEquiv _) (𝟙 (SheafOfModules.unit _))))
    rw [Category.id_comp, Equiv.apply_symm_apply] at h
    rw [SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply]
    exact h.symm
  inv_hom_id := by
    apply (constantUnitHomEquiv J _).injective
    have h := SheafOfModules.unitHomEquiv_comp_apply
      (𝟙 (SheafOfModules.unit ((constantSheaf J RingCat.{w}).obj (RingCat.of R))))
      ((SheafOfModules.unitHomEquiv _).symm
        (constantUnitHomEquiv J _ (𝟙 (constantModuleSheaf J (ModuleCat.of R R)))))
    rw [Category.id_comp, Equiv.apply_symm_apply] at h
    rw [constantUnitHomEquiv_comp, Equiv.apply_symm_apply]
    exact h.symm


/-- The free sheaf of modules on a finite type `I` is the constant sheaf of modules on the
free module on `I`. The coproduct is taken in `ModuleCat R`; it is preserved by the constant
sheaf functor because `I` is finite. -/
noncomputable def freeIsoConstantModuleSheaf (I : Type w) [Fintype I] [DecidableEq I] :
    SheafOfModules.free (R := (constantSheaf J RingCat.{w}).obj (RingCat.of R)) I ≅
      constantModuleSheaf J (∐ (fun _ : I => ModuleCat.of R R)) :=
  letI : HasColimitsOfShape (Discrete I) AddCommGrpCat.{w} := AddCommGrpCat.hasColimitsOfShape
  letI : HasColimitsOfShape (Discrete I)
      (PresheafOfModules.{w} ((constantSheaf J RingCat.{w}).obj (RingCat.of R)).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  letI : HasColimitsOfShape (Discrete I)
      (SheafOfModules.{w} ((constantSheaf J RingCat.{w}).obj (RingCat.of R))) :=
    SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _
  letI : HasColimitsOfShape (Discrete I) (PresheafOfModules.{w}
      ((presheafToSheaf J RingCat.{w}).obj ((Functor.const Cᵒᵖ).obj (RingCat.of R))).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  letI : HasColimitsOfShape (Discrete I) (SheafOfModules.{w}
      ((presheafToSheaf J RingCat.{w}).obj ((Functor.const Cᵒᵖ).obj (RingCat.of R)))) :=
    SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _
  letI e1 : SheafOfModules.free (R := (constantSheaf J RingCat.{w}).obj (RingCat.of R)) I ≅
      ∐ (fun _ : I => constantModuleSheaf J (ModuleCat.of R R)) :=
    HasColimit.isoOfNatIso (Discrete.natIso (fun _ => unitIsoConstantModuleSheaf J (R := R)))
  letI _hfc : PreservesColimitsOfShape (Discrete I) (constantModuleSheafFunctor J (R := R)) :=
    inferInstance
  e1 ≪≫ (HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete
      (fun _ : I => ModuleCat.of R R) (constantModuleSheafFunctor J (R := R)))).symm ≪≫
    (preservesColimitIso (constantModuleSheafFunctor J (R := R))
      (Discrete.functor (fun _ : I => ModuleCat.of R R))).symm

end Unit

section FinitePresentation

variable {R : Type w} [Ring R]
variable [HasWeakSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The coproduct of `I` copies of `R` in `ModuleCat R`, for a finite type `I`, is the standard
finite free module `I → R`. -/
noncomputable def coprodIsoPi (I : Type w) [Fintype I] [DecidableEq I] :
    (∐ (fun _ : I => ModuleCat.of R R)) ≅ ModuleCat.of R (I → R) :=
  ModuleCat.coprodIsoDirectSum _ ≪≫
    (DirectSum.linearEquivFunOnFintype R I (fun _ => R)).toModuleIso

/-- `SheafOfModules.free I`, for a finite index type `I`, is the constant sheaf of modules on the
standard finite free module `I → R`. -/
noncomputable def freeIsoPi (I : Type w) [Fintype I] [DecidableEq I] :
    SheafOfModules.free (R := (constantSheaf J RingCat.{w}).obj (RingCat.of R)) I ≅
      constantModuleSheaf J (ModuleCat.of R (I → R)) :=
  freeIsoConstantModuleSheaf J I ≪≫
    (constantModuleSheafFunctor J (R := R)).mapIso (coprodIsoPi I)

/-- The constant sheaf of modules functor takes epimorphisms to epimorphisms: it preserves
finite colimits, hence pushouts, hence epimorphisms. -/
lemma epi_constantModuleSheafMap {M N : ModuleCat.{w} R} (f : M ⟶ N) [Epi f] :
    Epi (constantModuleSheafMap J f) := by
  have h1 : PreservesColimitsOfShape WalkingSpan (constantModuleSheafFunctor J (R := R)) :=
    inferInstance
  have h2 : (constantModuleSheafFunctor J (R := R)).PreservesEpimorphisms := inferInstance
  exact @Functor.PreservesEpimorphisms.preserves _ _ _ _ _ h2 _ _ f ‹Epi f›

/-- The constant sheaf of modules on the kernel of a morphism of modules is the kernel of the
induced morphism of constant sheaves of modules: the constant sheaf functor is left exact. -/
noncomputable def kernelIsoConstant {M N : ModuleCat.{w} R} (f : M ⟶ N) :
    constantModuleSheaf J (kernel f) ≅ kernel (constantModuleSheafMap J f) :=
  PreservesKernel.iso (constantModuleSheafFunctor J (R := R)) f


variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks Project, Tag 093N, part (2), the forward implication.** On a site with a non sheaf
theoretically empty object, if the constant sheaf of modules on `M` is of finite presentation
then `M` is a finitely presented `R`-module.

This is the Stacks argument: part (1) makes `M` finite, a finite free presentation
`R^n ↠ M` is chosen, Tag 01BP makes the kernel of the resulting surjection `free (Fin n) ↠ M̲`
of finite type, left exactness of the constant sheaf functor identifies that kernel with the
constant sheaf on `ker (R^n → M)`, and part (1) again makes that kernel a finite module.

The hypotheses are exactly those of part (1). The form of Tag 01BP used is
`Stacks.SheafOfModules.SliceFinite.isFiniteType_kernel_of_generatingSections`, which assumes
neither products nor pullbacks on the site because the source of the surjection is generated by
finitely many *global* sections. -/
lemma finitePresentation_of_isFinitePresentation
    (hJ : ∃ U : C, ¬ (⊥ : Sieve U) ∈ J U) (M : ModuleCat.{w} R)
    [SheafOfModules.IsFinitePresentation (constantModuleSheaf J M)] :
    Module.FinitePresentation R M := by
  classical
  have hs0 : HasSheafify J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have hs1 : ∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{w} := fun _ =>
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have hMfin : Module.Finite R M := (constantModuleSheaf_isFiniteType_iff J hJ M).mp inferInstance
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let eI : (Fin n → R) ≃ₗ[R] (ULift.{w} (Fin n) → R) :=
    LinearEquiv.funCongrLeft R R (Equiv.ulift.{w, 0})
  let f' : (ULift.{w} (Fin n) → R) →ₗ[R] M := f ∘ₗ (eI.symm : _ →ₗ[R] (Fin n → R))
  have hf' : Function.Surjective f' := hf.comp eI.symm.surjective
  let φ : ModuleCat.of R (ULift.{w} (Fin n) → R) ⟶ M := ModuleCat.ofHom f'
  have hφ : Epi φ := (ModuleCat.epi_iff_surjective φ).mpr hf'
  have hφc : Epi (constantModuleSheafMap J φ) := epi_constantModuleSheafMap J φ
  have hpsi : Epi ((freeIsoPi J (ULift.{w} (Fin n))).hom ≫ constantModuleSheafMap J φ) :=
    epi_comp _ _
  have hgs : (SheafOfModules.free.generatingSections
      (R := (constantSheaf J RingCat.{w}).obj (RingCat.of R)) (ULift.{w} (Fin n))).IsFiniteType :=
    ⟨inferInstanceAs (Finite (ULift.{w} (Fin n)))⟩
  have hk : (kernel ((freeIsoPi J (ULift.{w} (Fin n))).hom ≫
      constantModuleSheafMap J φ)).IsFiniteType :=
    Stacks.SheafOfModules.SliceFinite.isFiniteType_kernel_of_generatingSections
      (SheafOfModules.free.generatingSections (ULift.{w} (Fin n))) _
  have e : kernel ((freeIsoPi J (ULift.{w} (Fin n))).hom ≫ constantModuleSheafMap J φ) ≅
      constantModuleSheaf J (kernel φ) :=
    kernelIsIsoComp (freeIsoPi J (ULift.{w} (Fin n))).hom (constantModuleSheafMap J φ) ≪≫
      (kernelIsoConstant J φ).symm
  have hkc : (constantModuleSheaf J (kernel φ)).IsFiniteType :=
    Stacks.SheafOfModules.SliceFinite.isFiniteType_of_epi e.hom hk
  have hkfin : ModuleCat.isFG R (kernel φ) :=
    (constantModuleSheaf_isFiniteType_iff J hJ (kernel φ)).mp hkc
  have hkfin0 : Module.Finite R (kernel φ : ModuleCat.{w} R) := hkfin
  have hkfin' : Module.Finite R (LinearMap.ker f') :=
    Module.Finite.equiv (ModuleCat.kernelIsoKer φ).toLinearEquiv
  exact Module.finitePresentation_of_surjective f' hf' (Module.Finite.iff_fg.mp hkfin')


end FinitePresentation



end Stacks.SheafOfModules.Constant

end
