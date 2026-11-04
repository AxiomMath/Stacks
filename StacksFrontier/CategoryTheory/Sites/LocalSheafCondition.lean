module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import StacksFrontier.CategoryTheory.Sites.LocalAmalgamation

/-!
# The sheaf condition for one topology is local for another

Let `C` carry two Grothendieck topologies `J` and `K`, and let `P` be a presheaf on `C` which is
a sheaf for `K`.  Suppose every object `U` of `C` admits a `K`-covering family on whose members
the restriction of `P` to the slice site is a sheaf for the localized topology `J.over V`.  Then
`P` is a sheaf for `J`.

This is the step that turns a *local* identification of a presheaf — "on a `K`-covering of every
object, `P` looks like something which is a `J`-sheaf" — into the `J`-sheaf condition itself.
The two topologies are unrelated: **`K ≤ J` is not assumed and is not used.**  What the proof
needs of `K` is only that `P` is a `K`-sheaf, so that the local amalgamations glue and so that
two sections agreeing on a `K`-covering are equal; and what it needs of `J` is only the
stability of its covering sieves under pullback.

## Main results

* `CategoryTheory.Presieve.isSheafFor_of_isSheaf_over`: the `J`-sheaf condition at an object
  `A.left` lying over `V`, extracted from the `J.over V`-sheaf condition of the restriction of
  `P` to the slice `C/V`.
* `CategoryTheory.Presieve.isSheaf_of_locally_isSheafFor`: **the locality of the sheaf
  condition**, in the form the proof actually uses: the `J`-sheaf condition is only needed at
  the domain of each member of one `K`-covering sieve of each object.
* `CategoryTheory.Presieve.isSheaf_of_locally_isSheaf_over` and
  `CategoryTheory.Presieve.isSheaf_of_locally_isSheaf_over_ofArrows`: the same with the local
  hypothesis in slice form, for a covering sieve and for a covering *family*.  The second is the
  shape a local-on-a-covering predicate such as quasi-coherence of Stacks 03DL (6) supplies:
  there the covering of an object is given as a family `V i ⟶ U` whose generated sieve covers,
  and the hypothesis is available at the `V i` only, not at every member of that sieve.
* `CategoryTheory.Presheaf.isSheaf_of_locally_isSheaf_over` and
  `CategoryTheory.Presheaf.isSheaf_of_locally_isSheaf_over_ofArrows`: both for a presheaf with
  values in an arbitrary category, which is the form a sheaf of modules consumes.

## Implementation notes

The proof is the standard one and is written out in four steps.  For a `J`-covering sieve `R` of
`U` and a compatible family `x` on `R`:

* on each member `f : V ⟶ U` of the `K`-covering sieve `T`, the pullback `R.pullback f` is a
  `J`-covering sieve of `V` and `x` pulls back to a compatible family on it, so the hypothesis at
  `f` gives a unique amalgamation `t_f ∈ P(V)`;
* the family `f ↦ t_f` is compatible, because for `g₁ ≫ f₁ = g₂ ≫ f₂` the two restrictions
  `P(g₁)(t_{f₁})` and `P(g₂)(t_{f₂})` both amalgamate the pullback of `x` along that common
  composite, and the hypothesis at the member `g₁ ≫ f₁` — which is a member of `T` because a
  sieve is downward closed — makes amalgamations over its domain unique;
* the `K`-sheaf condition amalgamates `f ↦ t_f` to an `s ∈ P(U)`, and `s` amalgamates `x`
  because the two agree after restriction along every member of `T.pullback h`, `P` being
  `K`-separated;
* uniqueness is the same argument once more: two amalgamations of `x` restrict to amalgamations
  of each `x.pullback f`, hence agree on `T`, hence are equal.

Downward closure of `T` is what lets the core statement ask for the `J`-sheaf condition only at
the domains of members of `T`, and it is also why the covering-*family* form needs
`isSheafFor_of_isSheaf_over` at an arbitrary object of the slice rather than at the tautological
one: a member of `Sieve.ofArrows V f` is only an `a ≫ f i`, so what the slice hypothesis at
`V i` has to supply is the sheaf condition at the domain of `a`, i.e. at the object `a` of
`C/(V i)`.

`CategoryTheory.SiteGlueing.isSheaf_of_isSheaf_over` in
`StacksFrontier/CategoryTheory/Sites/Glueing/AbsoluteGlueingAnySite.lean` is the degenerate case
`K = J`, `T = ⊤` of the main result, and the computation inside its proof is
`isSheafFor_of_isSheaf_over` at the tautological object `V/V`.  It is not restated in terms of
the results here, and the duplication is deliberate: that file is about glueing data on one
site and reading it through a second topology would only obscure it.

## References

* [Stacks Project, Tag 00VR](https://stacks.math.columbia.edu/tag/00VR)
* [Stacks Project, Tag 00ZB](https://stacks.math.columbia.edu/tag/00ZB)
-/

@[expose] public section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Presieve

/-- **The `J`-sheaf condition at an object over `V`, from the `J.over V`-sheaf condition of the
slice.**  If the restriction of `P` to the slice site `C/V` is a sheaf for the localized
topology `J.over V`, then for every object `A` of `C/V` and every `J`-covering sieve `S` of
`A.left`, the presheaf `P` satisfies the sheaf condition for `S`.

The sheaf condition for `S` matches, arrow by arrow, the sheaf condition on `C/V` at `A` for the
transported sieve `(Sieve.overEquiv A).symm S`. -/
public theorem isSheafFor_of_isSheaf_over {J : GrothendieckTopology C} {P : Cᵒᵖ ⥤ Type w}
    {V : C} (h : IsSheaf (J.over V) ((Over.forget V).op ⋙ P)) (A : Over V)
    {S : Sieve A.left} (hS : S ∈ J A.left) :
    IsSheafFor P (S : Presieve A.left) := by
  intro x hx
  set x' : FamilyOfElements ((Over.forget V).op ⋙ P)
      (((Sieve.overEquiv A).symm S : Sieve A) : Presieve A) :=
    fun _ g hg => x g.left ((Sieve.overEquiv_symm_iff S g).mp hg)
  have hx' : x'.Compatible := by
    intro b₁ b₂ W g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    exact hx g₁.left g₂.left _ _ (by simpa using (Over.forget V).congr_map hcomm)
  have amalg : ∀ t : P.obj (op A.left), x.IsAmalgamation t ↔ x'.IsAmalgamation t :=
    fun t => ⟨fun ht _ g _ => ht g.left _, fun ht _ g hg =>
      ht (Over.homMk g (by simp) : Over.mk (g ≫ A.hom) ⟶ A)
        ((Sieve.overEquiv_symm_iff S
          (Over.homMk g (by simp) : Over.mk (g ≫ A.hom) ⟶ A)).mpr hg)⟩
  obtain ⟨t, ht, huniq⟩ := h _ (J.overEquiv_symm_mem_over A S hS) x' hx'
  exact ⟨t, (amalg t).mpr ht, fun t' ht' => huniq t' ((amalg t').mp ht')⟩

/-- **The sheaf condition for `J` is local for `K`.**  Let `P` be a `K`-sheaf of types such that
every object `U` has a `K`-covering sieve `T` with the property that `P` satisfies the `J`-sheaf
condition at the domain of every member of `T`.  Then `P` is a sheaf for `J`.

`K ≤ J` is neither assumed nor used: the two topologies interact only through the hypotheses. -/
public theorem isSheaf_of_locally_isSheafFor {J K : GrothendieckTopology C} {P : Cᵒᵖ ⥤ Type w}
    (hK : IsSheaf K P)
    (hloc : ∀ U : C, ∃ T : Sieve U, T ∈ K U ∧ ∀ ⦃W : C⦄ ⦃g : W ⟶ U⦄, T g →
      ∀ {S : Sieve W}, S ∈ J W → IsSheafFor P (S : Presieve W)) :
    IsSheaf J P := by
  intro U R hR x hx
  obtain ⟨T, hTmem, hpt⟩ := hloc U
  have hpb : ∀ {V : C} (f : V ⟶ U), R.pullback f ∈ J V := fun f => J.pullback_stable f hR
  -- The restriction of a global amalgamation is a local amalgamation.
  have hpbam : ∀ {V : C} (f : V ⟶ U) {u : P.obj (op U)}, x.IsAmalgamation u →
      (x.pullback f).IsAmalgamation (P.map f.op u) := by
    intro V f u hu Z m hm
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    exact hu (m ≫ f) hm
  -- The local amalgamations on the members of `T`.
  have hex : ∀ {V : C} {f : V ⟶ U}, T f →
      ∃! t : P.obj (op V), (x.pullback f).IsAmalgamation t :=
    fun {V f} hf => hpt hf (hpb f) (x.pullback f) (hx.pullback f)
  set tfam : FamilyOfElements P (T : Presieve U) :=
    fun _ f hf => (hex hf).exists.choose
  have htfam : ∀ {V : C} {f : V ⟶ U} (hf : T f),
      (x.pullback f).IsAmalgamation (tfam f hf) := fun hf => (hex hf).exists.choose_spec
  -- A local amalgamation stays one after restriction.
  have hrestr : ∀ {V W : C} {f : V ⟶ U} (hf : T f) (a : W ⟶ V),
      (x.pullback (a ≫ f)).IsAmalgamation (P.map a.op (tfam f hf)) := by
    intro V W f hf a Z m hm
    have hm' : (R.pullback f) (m ≫ a) := by simpa using hm
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, htfam hf (m ≫ a) hm']
    exact x.congr_arrow (Category.assoc m a f) _ _
  -- Hence the local amalgamations form a compatible family on `T`.
  have hcompat : tfam.Compatible := by
    intro V₁ V₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    refine (hpt (T.downward_closed h₁ g₁) (hpb (g₁ ≫ f₁))).isSeparatedFor _ _ _
      (hrestr h₁ g₁) ?_
    rw [hcomm]
    exact hrestr h₂ g₂
  obtain ⟨s, hs, -⟩ := hK T hTmem tfam hcompat
  -- `s` amalgamates `x`, because it does so locally on `T` and `P` is `K`-separated.
  have hsamalg : x.IsAmalgamation s := by
    intro W h hRh
    refine (hK (T.pullback h) (K.pullback_stable h hTmem)).isSeparatedFor
      (fun _ k hk => x (k ≫ h) (R.downward_closed hRh k)) _ _ ?_
      fun _ k _ => (hx.to_sieveCompatible h k hRh).symm
    intro Z k hk
    have h1 : tfam (k ≫ h) hk = x (k ≫ h) (R.downward_closed hRh k) :=
      (hpt hk (hpb (k ≫ h))).isSeparatedFor _ _ _ (htfam hk) fun _ m _ =>
        (hx.to_sieveCompatible (k ≫ h) m (R.downward_closed hRh k)).symm
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, hs (k ≫ h) hk, h1]
  refine ⟨s, hsamalg, fun t ht => ?_⟩
  exact (hK T hTmem).isSeparatedFor (fun _ f _ => P.map f.op t) _ _ (fun _ _ _ => rfl)
    fun _ f hf => (hpt hf (hpb f)).isSeparatedFor _ _ _ (hpbam f hsamalg) (hpbam f ht)

/-- **The sheaf condition for `J` is local for `K`**, with the local hypothesis in slice form: a
`K`-sheaf of types whose restriction to the slice site at the domain of each member of a
`K`-covering sieve of each object is a sheaf for the localized topology `J.over V`, is a sheaf
for `J`. -/
public theorem isSheaf_of_locally_isSheaf_over {J K : GrothendieckTopology C} {P : Cᵒᵖ ⥤ Type w}
    (hK : IsSheaf K P)
    (hloc : ∀ U : C, ∃ T : Sieve U, T ∈ K U ∧
      ∀ ⦃V : C⦄ ⦃f : V ⟶ U⦄, T f → IsSheaf (J.over V) ((Over.forget V).op ⋙ P)) :
    IsSheaf J P := by
  refine isSheaf_of_locally_isSheafFor hK fun U => ?_
  obtain ⟨T, hTmem, hT⟩ := hloc U
  exact ⟨T, hTmem, fun {_W} {_g} hg _ hS =>
    isSheafFor_of_isSheaf_over (hT hg) (Over.mk (𝟙 _)) hS⟩

/-- **The sheaf condition for `J` is local for `K`**, with the local hypothesis given on a
covering *family* rather than on a covering sieve.  This is the shape in which a
local-on-a-covering predicate such as quasi-coherence of Stacks 03DL (6) supplies its covering:
an indexed family `V i ⟶ U` whose generated sieve is a `K`-covering sieve, with the hypothesis
available at the `V i` only.

A member of `Sieve.ofArrows V f` is an `a ≫ f i`, so the sheaf condition is needed at the
domain of `a`; that is `isSheafFor_of_isSheaf_over` at the object `a` of the slice `C/(V i)`. -/
public theorem isSheaf_of_locally_isSheaf_over_ofArrows {J K : GrothendieckTopology C}
    {P : Cᵒᵖ ⥤ Type w} (hK : IsSheaf K P)
    (hloc : ∀ U : C, ∃ (I : Type*) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ K U ∧
        ∀ i, IsSheaf (J.over (V i)) ((Over.forget (V i)).op ⋙ P)) :
    IsSheaf J P := by
  refine isSheaf_of_locally_isSheafFor hK fun U => ?_
  obtain ⟨I, V, f, hmem, hT⟩ := hloc U
  refine ⟨Sieve.ofArrows V f, hmem, fun {W} {g} hg {S} hS => ?_⟩
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff V f g).1 hg
  exact isSheafFor_of_isSheaf_over (hT i) (Over.mk a) hS

end Presieve

namespace Presheaf

variable {A : Type*} [Category* A]

/-- **The sheaf condition for `J` is local for `K`**, for a presheaf with values in an arbitrary
category: the sheaf condition is the one of `CategoryTheory.Presieve` for every corepresentable
presheaf of types, and the hypotheses are inherited by each of them. -/
public theorem isSheaf_of_locally_isSheaf_over {J K : GrothendieckTopology C} {P : Cᵒᵖ ⥤ A}
    (hK : IsSheaf K P)
    (hloc : ∀ U : C, ∃ T : Sieve U, T ∈ K U ∧
      ∀ ⦃V : C⦄ ⦃f : V ⟶ U⦄, T f → IsSheaf (J.over V) ((Over.forget V).op ⋙ P)) :
    IsSheaf J P := by
  intro E
  refine Presieve.isSheaf_of_locally_isSheaf_over (hK E) fun U => ?_
  obtain ⟨T, hTmem, hT⟩ := hloc U
  exact ⟨T, hTmem, fun {_V} {_f} hf => hT hf E⟩

/-- **The sheaf condition for `J` is local for `K`** for a presheaf with values in an arbitrary
category, with the local hypothesis given on a covering family. -/
public theorem isSheaf_of_locally_isSheaf_over_ofArrows {J K : GrothendieckTopology C}
    {P : Cᵒᵖ ⥤ A} (hK : IsSheaf K P)
    (hloc : ∀ U : C, ∃ (I : Type*) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ K U ∧
        ∀ i, IsSheaf (J.over (V i)) ((Over.forget (V i)).op ⋙ P)) :
    IsSheaf J P := by
  intro E
  refine Presieve.isSheaf_of_locally_isSheaf_over_ofArrows (hK E) fun U => ?_
  obtain ⟨I, V, f, hmem, hT⟩ := hloc U
  exact ⟨I, V, f, hmem, fun i => hT i E⟩

end Presheaf

end CategoryTheory

end
