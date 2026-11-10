module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ChosenCoverings

/-!
# Gluing a sheaf out of representable subsheaves

Let `F` be a presheaf of sets on the big fppf site over a scheme `S` which is a sheaf for the
*Zariski* topology, and let `(G i)` be a family of subfunctors of `F` which are fppf sheaves and
whose inclusions are representable by algebraic spaces. If the union of the `G i` is all of `F`
locally for the fppf topology, then `F` is itself an fppf sheaf.

## Main results

* `AlgebraicGeometry.Space.isSheaf_of_locallySurjective_representable_subfunctors`:
  **Stacks 07WE**, the fppf sheaf condition from those hypotheses.

## Implementation notes

The union of the subfunctors is their supremum in the lattice of subfunctors, and the covering
hypothesis is local surjectivity of its inclusion into `F`. Stated that way the index type may
live in any universe, and no coproduct universe has to be chosen.

Given a compatible family of sections over an fppf covering sieve of `U`, the covering is first
refined so that each member carries a section of one of the `G i`. The image of such a member is
an open subscheme of `U`, over which the section descends — the member covers its image by a
single flat, surjective morphism locally of finite presentation, hence by a one-element fppf
covering, and a representable subfunctor of `F` is separated enough for the descended section to
be unique. Those opens cover `U`, so the Zariski sheaf condition on `F` amalgamates the descended
sections, and the amalgamation restricts to the given family because two sections of `F` which
agree locally on a representable subfunctor agree.

Representability enters only through separatedness: for `s` a section of `F` over `U`, the fibre
product of `yoneda.obj U ⟶ F` with the inclusion of `G i` is an algebraic space, hence an fppf
sheaf, and `yoneda.obj U` is one because the topology of a big fppf site is subcanonical.

## References

* [Stacks Project, Tag 07WE](https://stacks.math.columbia.edu/tag/07WE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w x

namespace AlgebraicGeometry.Space

/-! ### Fppf coverings of the big site over a base -/

/-- Every covering sieve of the big fppf site over `S` is refined by the family of a covering. -/
theorem exists_overCovering_refining_sieve
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U : BigFppfOver B S hS} {R : Sieve U} (hR : R ∈ BigFppfOver.topology B S hS U) :
    ∃ E : PreZeroHypercover.{u + 1} U,
      BigFppfOver.IsCovering B S hS ⟨U, E⟩ ∧ E.presieve₀ ≤ R := by
  rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨E, hE, hle⟩ := exists_covering_refining_sieve B hR
  refine ⟨⟨E.I₀, fun i ↦ Over.mk (E.f i ≫ U.hom), fun i ↦ Over.homMk (E.f i) rfl⟩, ?_, ?_⟩
  · change B.IsCovering ⟨U.left, _⟩
    simpa [PreZeroHypercover.map] using hE
  · rw [Presieve.ofArrows_le_iff]
    intro i
    exact (Sieve.overEquiv_iff R (E.f i)).mp (hle _ _ ⟨i⟩)

/-- A one-element family in the big fppf site over `S` whose underlying morphism of schemes is
flat, surjective and locally of finite presentation generates a covering sieve. -/
private theorem singleton_mem_topology_over_of_fppf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V U : BigFppfOver B S hS} (f : V ⟶ U)
    (hflat : Flat (B.inclusion.map f.left)) (hsurj : Surjective (B.inclusion.map f.left))
    (hlfp : LocallyOfFinitePresentation (B.inclusion.map f.left)) :
    Sieve.generate (Presieve.singleton f) ∈ BigFppfOver.topology B S hS U := by
  have hbase : Sieve.generate (Presieve.singleton f.left) ∈ B.topology U.left := by
    have hfp : IsFppfCovering
        (⟨U.left, PreZeroHypercover.singleton f.left⟩ : Covering B.Schemes) := by
      change (PreZeroHypercover.singleton f.left).presieve₀ ∈
        Scheme.fppfPrecoverage.comap B.inclusion U.left
      rw [Precoverage.mem_comap_iff, PreZeroHypercover.presieve₀_singleton,
        Presieve.map_singleton]
      have : Flat (B.inclusion.map f.left) := hflat
      have : Surjective (B.inclusion.map f.left) := hsurj
      have : LocallyOfFinitePresentation (B.inclusion.map f.left) := hlfp
      exact (B.inclusion.map f.left).singleton_mem_fppfPrecoverage
    simpa [PreZeroHypercover.presieve₀_singleton] using
      B.generate_mem_topology_of_isFppfCovering (PreZeroHypercover.singleton f.left) hfp
  rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate,
    ← Sieve.arrows_generate_map_eq_functorPushforward]
  simpa using hbase

/-! ### The open subscheme cut out by the image of a covering member -/

/-- The underlying object of `Sch_κ` of an open subscheme of an object of the big fppf site
over `S`: an open subscheme is no larger than its ambient scheme, so it still satisfies the
site's size cutoff. -/
private noncomputable def openSubscheme
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) : B.Schemes :=
  ⟨V.toScheme, (Scheme.size_coe_opens_le _ V).trans_lt U.left.2⟩

/-- The object of the big fppf site over `S` given by an open subscheme of an object `U`, with
the structure morphism obtained by composing with that of `U`. -/
private noncomputable def openSubobject
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) : BigFppfOver B S hS :=
  Over.mk ((ObjectProperty.homMk (Scheme.Opens.ι V) :
    openSubscheme B S hS U V ⟶ U.left) ≫ U.hom)

/-- The inclusion of an open subobject into `U`, in the big fppf site over `S`. -/
private noncomputable def openSubobjectInclusion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) : openSubobject B S hS U V ⟶ U :=
  Over.homMk (ObjectProperty.homMk (Scheme.Opens.ι V)) (by simp [openSubobject])

/-- A morphism of schemes whose range lands in an open subscheme satisfies, after factoring
through that open subscheme, every property stable under base change: the factorization is a
base change of the original morphism along the open immersion. -/
private theorem prop_lift_of_range_subset (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens)
    (hRange : Set.range f ⊆ Set.range (Scheme.Opens.ι W)) (hf : P f) :
    P (IsOpenImmersion.lift (Scheme.Opens.ι W) f hRange) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsOpenImmersion.isPullback_lift_id f (Scheme.Opens.ι W) hRange).flip hf

/-- A morphism of schemes whose range is *exactly* an open subscheme becomes surjective after
factoring through that open subscheme. -/
private theorem surjective_lift_of_range_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens)
    (hRange : Set.range f = Set.range (Scheme.Opens.ι W)) :
    Surjective (IsOpenImmersion.lift (Scheme.Opens.ι W) f hRange.le) := by
  refine ⟨fun y ↦ ?_⟩
  have hy : y.1 ∈ Set.range f := by
    rw [hRange]
    simpa using y.2
  obtain ⟨z, hz⟩ := Set.mem_range.mp hy
  refine ⟨z, Subtype.ext ?_⟩
  calc (IsOpenImmersion.lift (Scheme.Opens.ι W) f hRange.le z).1 =
      (Scheme.Opens.ι W) (IsOpenImmersion.lift (Scheme.Opens.ι W) f hRange.le z) := rfl
    _ = f z := by rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac]
    _ = y.1 := hz

/-- The factorization of a morphism of the big fppf site over `S` through an open subobject of
its target containing its image. -/
private noncomputable def factorThroughOpenSubobject
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A U : BigFppfOver B S hS) (f : A ⟶ U)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (hf : Set.range ((BigFppfOver.toScheme B S hS).map f) ⊆ V) :
    A ⟶ openSubobject B S hS U V := by
  have hRange : Set.range ((BigFppfOver.toScheme B S hS).map f) ⊆
      Set.range (Scheme.Opens.ι V) := by simpa using hf
  have : IsOpenImmersion (Scheme.Opens.ι V) := Scheme.Opens.instIsOpenImmersionι V
  have hRange' : Set.range (B.inclusion.map f.left) ⊆ Set.range (Scheme.Opens.ι V) := by
    simpa [BigFppfOver.toScheme] using hRange
  let l' : B.inclusion.obj A.left ⟶ V.toScheme :=
    IsOpenImmersion.lift (Scheme.Opens.ι V) (B.inclusion.map f.left) hRange'
  let l : B.inclusion.obj A.left ⟶ B.inclusion.obj (openSubscheme B S hS U V) := l'
  let fl : A.left ⟶ openSubscheme B S hS U V :=
    B.inclusion.preimage (X := A.left) (Y := openSubscheme B S hS U V) l
  refine Over.homMk fl ?_
  apply B.inclusion.map_injective
  have hl0 : l' ≫ Scheme.Opens.ι V = B.inclusion.map f.left :=
    IsOpenImmersion.lift_fac (f := Scheme.Opens.ι V) (g := B.inclusion.map f.left) hRange'
  have hl : l ≫ Scheme.Opens.ι V = (BigFppfOver.toScheme B S hS).map f := by
    change l' ≫ Scheme.Opens.ι V = B.inclusion.map f.left
    simpa [BigFppfOver.toScheme] using hl0
  dsimp only [openSubobject]
  change B.inclusion.map fl ≫ Scheme.Opens.ι V ≫ B.inclusion.map U.hom = B.inclusion.map A.hom
  rw [B.inclusion.map_preimage]
  calc l ≫ Scheme.Opens.ι V ≫ B.inclusion.map U.hom =
      (l ≫ Scheme.Opens.ι V) ≫ B.inclusion.map U.hom := rfl
    _ = (BigFppfOver.toScheme B S hS).map f ≫ B.inclusion.map U.hom := by rw [hl]
    _ = B.inclusion.map A.hom := by
        change B.inclusion.map (f.left ≫ U.hom) = _
        rw [f.w]

/-- On underlying schemes, the factorization through an open subobject is the lift of the morphism
through the open immersion. -/
private theorem map_factorThroughOpenSubobject_left
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A U : BigFppfOver B S hS) (f : A ⟶ U)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (hf : Set.range ((BigFppfOver.toScheme B S hS).map f) ⊆ V)
    (hRange : Set.range (B.inclusion.map f.left) ⊆ Set.range (Scheme.Opens.ι V)) :
    B.inclusion.map (factorThroughOpenSubobject B S hS A U f V hf).left =
      IsOpenImmersion.lift (Scheme.Opens.ι V) (B.inclusion.map f.left) hRange := by
  change B.inclusion.map (B.inclusion.preimage
    (X := A.left) (Y := openSubscheme B S hS U V)
    (IsOpenImmersion.lift (H := Scheme.Opens.instIsOpenImmersionι _)
      (Scheme.Opens.ι V) (B.inclusion.map f.left) _)) = _
  exact B.inclusion.map_preimage _

/-- The factorization through an open subobject does compose back to the original morphism. -/
private theorem factorThroughOpenSubobject_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A U : BigFppfOver B S hS) (f : A ⟶ U)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (hf : Set.range ((BigFppfOver.toScheme B S hS).map f) ⊆ V) :
    factorThroughOpenSubobject B S hS A U f V hf ≫ openSubobjectInclusion B S hS U V = f := by
  have : IsOpenImmersion (Scheme.Opens.ι V) := Scheme.Opens.instIsOpenImmersionι V
  have hRange' : Set.range (B.inclusion.map f.left) ⊆ Set.range (Scheme.Opens.ι V) := by
    simpa [BigFppfOver.toScheme] using (show
      Set.range ((BigFppfOver.toScheme B S hS).map f) ⊆ Set.range (Scheme.Opens.ι V) from
        by simpa using hf)
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  change B.inclusion.map (factorThroughOpenSubobject B S hS A U f V hf).left ≫
    B.inclusion.map (openSubobjectInclusion B S hS U V).left = B.inclusion.map f.left
  rw [map_factorThroughOpenSubobject_left B S hS A U f V hf hRange']
  simp [openSubobjectInclusion, openSubobject, openSubscheme, BigFppfOver.toScheme]

/-- An open cover of the underlying scheme of an object of `Sch_κ`, read as a family inside
`Sch_κ`. -/
private noncomputable def boundedOpenCover
    (B : BigFppfSite.{u}) (T : B.Schemes) (O : (B.inclusion.obj T).OpenCover.{u + 1}) :
    PreZeroHypercover.{u + 1} T where
  I₀ := O.I₀
  X i := ⟨O.X i, Scheme.size_lt_of_isOpenImmersion (O.f i) T.2⟩
  f i := ObjectProperty.homMk (O.f i)

/-- An open cover of the underlying scheme of an object `U` of the big fppf site over `S`
generates a covering sieve for the Zariski topology over `S`. -/
private theorem openCover_sieve_mem_zariskiTopology_over
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
    (O : (B.inclusion.obj U.left).OpenCover.{u + 1}) :
    Sieve.generate (Presieve.ofArrows
      (fun i : O.I₀ ↦ Over.mk ((boundedOpenCover B U.left O).f i ≫ U.hom))
      (fun i ↦ Over.homMk ((boundedOpenCover B U.left O).f i) (by simp))) ∈
      B.zariskiTopology.over (B.obj hS) U := by
  let E := boundedOpenCover B U.left O
  have hZ : IsZariskiCovering (⟨U.left, E⟩ : Covering B.Schemes) := by
    change (E.map B.inclusion).presieve₀ ∈ Scheme.zariskiPrecoverage _
    simpa [E, boundedOpenCover, PreZeroHypercover.map] using O.mem₀
  obtain ⟨⟨T', E'⟩, hE', hCE⟩ := B.zariskiCovering_has_representative ⟨U.left, E⟩ hZ
  obtain ⟨hbase, hfamily⟩ := hCE
  change U.left = T' at hbase
  cases hbase
  have hgen : Sieve.generate E.presieve₀ ∈ B.zariskiTopology U.left := by
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent
      (show PreZeroHypercover.CombinatoriallyEquivalent E E' by simpa using hfamily)]
    exact Precoverage.generate_mem_toGrothendieck ⟨E', rfl, hE'⟩
  let Eover : PreZeroHypercover.{u + 1} U :=
    ⟨E.I₀, fun i ↦ Over.mk (E.f i ≫ U.hom), fun i ↦ Over.homMk (E.f i) (by simp)⟩
  have hgenOver : Sieve.generate Eover.presieve₀ ∈ B.zariskiTopology.over (B.obj hS) U := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate,
      ← Sieve.arrows_generate_map_eq_functorPushforward]
    simpa [Eover, PreZeroHypercover.presieve₀, PreZeroHypercover.map] using hgen
  simpa [E, Eover, boundedOpenCover, PreZeroHypercover.presieve₀] using hgenOver

/-- Open subobjects of `U` whose union is all of `U` generate a covering sieve for the Zariski
topology over `S`. -/
private theorem openSubobject_sieve_mem_zariskiTopology_over
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
    {A : Type (u + 1)} (W : A → ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (hW : ∀ z, ∃ a, z ∈ W a) :
    Sieve.generate (Presieve.ofArrows (fun a ↦ openSubobject B S hS U (W a))
      (fun a ↦ openSubobjectInclusion B S hS U (W a))) ∈
      B.zariskiTopology.over (B.obj hS) U := by
  let O : ((BigFppfOver.toScheme B S hS).obj U).OpenCover.{u + 1} :=
    { I₀ := A
      X a := (W a).toScheme
      f a := Scheme.Opens.ι (W a)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun z ↦ ?_, fun a ↦ Scheme.Opens.instIsOpenImmersionι (W a)⟩
        obtain ⟨a, ha⟩ := hW z
        exact ⟨a, ⟨z, ha⟩, rfl⟩ }
  convert openCover_sieve_mem_zariskiTopology_over B S hS U O using 1
  rfl

/-- The members of a covering of the big fppf site over `S` are jointly surjective, flat and
locally of finite presentation. -/
private theorem isCovering_surjective_flat_locallyOfFinitePresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U : BigFppfOver B S hS}
    {E : PreZeroHypercover.{u + 1} U} (hE : BigFppfOver.IsCovering B S hS ⟨U, E⟩) :
    (∀ z : B.inclusion.obj U.left, ∃ a, z ∈ Set.range (B.inclusion.map (E.f a).left)) ∧
      ∀ a, Flat (B.inclusion.map (E.f a).left) ∧
        LocallyOfFinitePresentation (B.inclusion.map (E.f a).left) := by
  let ESch := (E.map (BigFppfOver.forget B S hS)).map B.inclusion
  have hEfp : ESch.presieve₀ ∈ Scheme.fppfPrecoverage (B.inclusion.obj U.left) := by
    have hbase := B.isFppfCovering_of_isCovering hE
    change (E.map (BigFppfOver.forget B S hS)).presieve₀ ∈
      Scheme.fppfPrecoverage.comap B.inclusion U.left at hbase
    rw [Precoverage.mem_comap_iff] at hbase
    simpa [ESch, PreZeroHypercover.map] using hbase
  rw [Scheme.fppfPrecoverage_eq_inf] at hEfp
  have hdata := (Scheme.presieve₀_mem_precoverage_iff ESch).1 hEfp.1
  have hdataLfp := (Scheme.presieve₀_mem_precoverage_iff
    (P := @LocallyOfFinitePresentation) ESch).1 hEfp.2
  exact ⟨hdata.1, fun a ↦ ⟨hdata.2 a, hdataLfp.2 a⟩⟩

/-- A flat morphism locally of finite presentation of the big fppf site over `S` covers its open
image by itself. -/
private theorem singleton_factorThroughOpenSubobject_mem_topology
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {V U : BigFppfOver B S hS}
    (f : V ⟶ U) (W : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (hW : Set.range (B.inclusion.map f.left) = (W : Set ((BigFppfOver.toScheme B S hS).obj U)))
    (hflat : Flat (B.inclusion.map f.left))
    (hlfp : LocallyOfFinitePresentation (B.inclusion.map f.left))
    (hf : Set.range ((BigFppfOver.toScheme B S hS).map f) ⊆ W) :
    Sieve.generate (Presieve.singleton (factorThroughOpenSubobject B S hS V U f W hf)) ∈
      BigFppfOver.topology B S hS (openSubobject B S hS U W) := by
  have hRange : Set.range (B.inclusion.map f.left) = Set.range (Scheme.Opens.ι W) :=
    hW.trans (Scheme.Opens.range_ι W).symm
  have himageMap := map_factorThroughOpenSubobject_left B S hS V U f W hf hRange.le
  refine singleton_mem_topology_over_of_fppf B S hS (factorThroughOpenSubobject B S hS V U f W hf)
    ?_ ?_ ?_ <;> rw [himageMap]
  · exact prop_lift_of_range_subset _ _ W hRange.le hflat
  · exact surjective_lift_of_range_eq _ W hRange
  · exact prop_lift_of_range_subset _ _ W hRange.le hlfp

/-! ### Separatedness supplied by a representable subfunctor -/

/-- A section of a sheaf `Q` which lifts along an injective map from a sheaf `P` locally on a
covering sieve lifts globally. -/
private theorem exists_lift_of_sheaf_on_covering_sieve
    {C : Type w} [Category.{v} C] {J : GrothendieckTopology C} {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q)
    (hP : Presheaf.IsSheaf J P) (hQ : Presheaf.IsSheaf J Q)
    (hf : ∀ X : C, Function.Injective (f.app (op X)))
    (U : C) (R : Sieve U) (hR : R ∈ J U) (s : Q.obj (op U))
    (hloc : ∀ ⦃V : C⦄ (g : V ⟶ U), R g → ∃ t : P.obj (op V), f.app (op V) t = Q.map g.op s) :
    ∃ t : P.obj (op U), f.app (op U) t = s := by
  classical
  let x : R.arrows.FamilyOfElements P := fun _ g hg ↦ Classical.choose (hloc g hg)
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hw
    apply hf Z
    calc f.app (op Z) (P.map g₁.op (x f₁ h₁)) =
        Q.map g₁.op (f.app (op Y₁) (x f₁ h₁)) := f.naturality_apply g₁.op _
      _ = Q.map g₁.op (Q.map f₁.op s) := by rw [Classical.choose_spec (hloc f₁ h₁)]
      _ = Q.map (g₁ ≫ f₁).op s := by simp
      _ = Q.map (g₂ ≫ f₂).op s := by rw [hw]
      _ = Q.map g₂.op (Q.map f₂.op s) := by simp
      _ = Q.map g₂.op (f.app (op Y₂) (x f₂ h₂)) := by rw [Classical.choose_spec (hloc f₂ h₂)]
      _ = f.app (op Z) (P.map g₂.op (x f₂ h₂)) := (f.naturality_apply g₂.op _).symm
  refine ⟨(hP.isSheafFor R hR).amalgamate x hx, ?_⟩
  apply (hQ.isSheafFor R hR).isSeparatedFor.ext
  intro V g hg
  calc Q.map g.op (f.app (op U) ((hP.isSheafFor R hR).amalgamate x hx)) =
      f.app (op V) (P.map g.op ((hP.isSheafFor R hR).amalgamate x hx)) :=
        (f.naturality_apply g.op _).symm
    _ = f.app (op V) (x g hg) := by rw [(hP.isSheafFor R hR).valid_glue hx g hg]
    _ = Q.map g.op s := Classical.choose_spec (hloc g hg)

/-- A section of a sheaf over the source of a one-element covering descends to the target, as
soon as it is compatible with the two projections of that covering. -/
private theorem exists_section_of_sheaf_of_covering_singleton
    {C : Type w} [Category.{v} C] {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf J F) {V U : C} (f : V ⟶ U)
    (hf : Sieve.generate (Presieve.singleton f) ∈ J U) (s : F.obj (op V))
    (hcompat : ∀ ⦃Z : C⦄ (p₁ p₂ : Z ⟶ V), p₁ ≫ f = p₂ ≫ f → F.map p₁.op s = F.map p₂.op s) :
    ∃ t : F.obj (op U), F.map f.op t = s := by
  have hsingleton : Presieve.IsSheafFor F (Presieve.singleton f) :=
    (Presieve.isSheafFor_iff_generate (Presieve.singleton f)).2
      (hF.isSheafFor (Sieve.generate (Presieve.singleton f)) hf)
  rw [Presieve.isSheafFor_singleton] at hsingleton
  obtain ⟨t, ht, _⟩ := hsingleton s (by
    intro Z p₁ p₂ hp
    exact @hcompat Z p₁ p₂ hp)
  exact ⟨t, ht⟩

/-- A section of `F` lying in a subfunctor `G` locally on a covering sieve lies in `G`, provided
the fibre product of the section with the inclusion of `G` is a sheaf and so is the representable
presheaf of the test object. -/
private theorem section_mem_subfunctor_of_local_lifts
    {C : Type w} [Category.{u} C] {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type u}
    (U : C) (R : Sieve U) (hR : R ∈ J U) (G : Subfunctor F) (s : F.obj (op U))
    (hP : Presheaf.IsSheaf J (pullback ((yonedaEquiv (F := F)).symm s) G.ι))
    (hY : Presheaf.IsSheaf J (yoneda.obj U))
    (hloc : ∀ ⦃V : C⦄ (g : V ⟶ U), R g →
      ∃ t : G.toFunctor.obj (op V), G.ι.app (op V) t = F.map g.op s) :
    ∃ t : G.toFunctor.obj (op U), G.ι.app (op U) t = s := by
  let ξ : yoneda.obj U ⟶ F := (yonedaEquiv (F := F)).symm s
  let f : pullback ξ G.ι ⟶ yoneda.obj U := pullback.fst ξ G.ι
  have hf (X : C) : Function.Injective (f.app (op X)) := injective_of_mono _
  have hloc' : ∀ ⦃V : C⦄ (g : V ⟶ U), R g →
      ∃ p : (pullback ξ G.ι).obj (op V), f.app (op V) p = (yoneda.obj U).map g.op (𝟙 U) := by
    intro V g hg
    obtain ⟨t, ht⟩ := hloc g hg
    let η : yoneda.obj V ⟶ G.toFunctor := (yonedaEquiv (F := G.toFunctor)).symm t
    have hc : yoneda.map g ≫ ξ = η ≫ G.ι := by
      apply (yonedaEquiv (F := F)).injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map,
        show ξ.app (op V) g = F.map g.op s by simp [ξ]]
      simpa [η] using ht.symm
    refine ⟨(pullback.lift (yoneda.map g) η hc).app (op V) (𝟙 V), ?_⟩
    have h := congrArg (fun k : yoneda.obj V ⟶ yoneda.obj U ↦ k.app (op V) (𝟙 V))
      (pullback.lift_fst (yoneda.map g) η hc)
    exact h.trans (by simp)
  obtain ⟨p, hp⟩ := exists_lift_of_sheaf_on_covering_sieve f hP hY hf U R hR (𝟙 U) hloc'
  refine ⟨(pullback.snd ξ G.ι).app (op U) p, ?_⟩
  have hcone := congrArg (fun η : pullback ξ G.ι ⟶ F ↦ η.app (op U) p)
    (pullback.condition (f := ξ) (g := G.ι))
  change ξ.app (op U) ((pullback.fst ξ G.ι).app (op U) p) =
    G.ι.app (op U) ((pullback.snd ξ G.ι).app (op U) p) at hcone
  rw [show (pullback.fst ξ G.ι).app (op U) p = 𝟙 U by simpa [f] using hp] at hcone
  simpa [ξ, yonedaEquiv_symm_app_apply] using hcone.symm

/-- The previous statement for the big fppf site over `S`, where both sheaf hypotheses come for
free: the fibre product is an algebraic space because the inclusion of the subfunctor is
representable by algebraic spaces, and the representable presheaf is a sheaf because the
topology is subcanonical. -/
private theorem section_mem_subfunctor_of_representable_local_lifts
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (G : Subfunctor F)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS G.ι)
    (U : BigFppfOver B S hS) (R : Sieve U) (hR : R ∈ BigFppfOver.topology B S hS U)
    (s : F.obj (op U))
    (hloc : ∀ ⦃V : BigFppfOver B S hS⦄ (g : V ⟶ U), R g →
      ∃ t : G.toFunctor.obj (op V), G.ι.app (op V) t = F.map g.op s) :
    ∃ t : G.toFunctor.obj (op U), G.ι.app (op U) t = s := by
  let _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  let _ : (BigFppfOver.topology B S hS).Subcanonical := inferInstance
  refine section_mem_subfunctor_of_local_lifts U R hR G s
    (hrep U ((yonedaEquiv (F := F)).symm s)).isSheaf ?_ hloc
  exact (isSheaf_iff_isSheaf_of_type (J := BigFppfOver.topology B S hS) (yoneda.obj U)).2
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := BigFppfOver.topology B S hS) (yoneda.obj U))

/-- Two sections of `F` over the same object, one of which comes from a subfunctor whose
inclusion is representable by algebraic spaces, are equal as soon as they agree on a covering
sieve. -/
private theorem section_eq_of_locally_eq_to_representable_subfunctor
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (G : Subfunctor F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G.toFunctor)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS G.ι)
    (U : BigFppfOver B S hS) (R : Sieve U) (hR : R ∈ BigFppfOver.topology B S hS U)
    (s : G.toFunctor.obj (op U)) (t : F.obj (op U))
    (hloc : ∀ ⦃V : BigFppfOver B S hS⦄ (g : V ⟶ U), R g →
      F.map g.op (G.ι.app (op U) s) = F.map g.op t) :
    G.ι.app (op U) s = t := by
  obtain ⟨t', ht'⟩ := section_mem_subfunctor_of_representable_local_lifts B S hS F G hrep U R hR t
    fun {V} g hg ↦ ⟨G.toFunctor.map g.op s,
      ((G.ι.naturality_apply g.op s).symm).trans (hloc g hg)⟩
  have hst : s = t' := by
    apply (hG.isSheafFor R hR).isSeparatedFor.ext
    intro V g hg
    apply injective_of_mono (G.ι.app (op V))
    calc G.ι.app (op V) (G.toFunctor.map g.op s) =
        F.map g.op (G.ι.app (op U) s) := (G.ι.naturality_apply g.op s).symm
      _ = F.map g.op t := hloc g hg
      _ = F.map g.op (G.ι.app (op U) t') := by rw [ht']
      _ = G.ι.app (op V) (G.toFunctor.map g.op t') := G.ι.naturality_apply g.op t'
  rw [hst, ht']

/-! ### Refining a covering so that every member carries a section of one subfunctor -/

/-- A section of `F` lies, locally on a covering sieve, in one of a family of subfunctors whose
union is locally all of `F`. -/
private theorem exists_local_iSup_section
    {C : Type w} [Category.{v} C] {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type u} {I : Type x}
    (G : I → Subfunctor F) (hcover : Presheaf.IsLocallySurjective J (iSup G).ι)
    (U : C) (s : F.obj (op U)) :
    ∃ R : Sieve U, R ∈ J U ∧ ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      ∃ (i : I) (t : (G i).toFunctor.obj (op V)), (G i).ι.app (op V) t = F.map f.op s := by
  refine ⟨Presheaf.imageSieve (iSup G).ι s, Presheaf.imageSieve_mem J (iSup G).ι s, ?_⟩
  intro V f hf
  simp only [Presheaf.imageSieve_apply] at hf
  obtain ⟨y, hy⟩ := hf
  have hmem : (iSup G).ι.app (op V) y ∈ (iSup G).obj (op V) := by simpa using y.2
  rw [Subfunctor.iSup_obj] at hmem
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
  exact ⟨i, ⟨(iSup G).ι.app (op V) y, hi⟩, hy⟩

/-- A covering of `U` refining a sieve can be refined further so that, over every member, the
given compatible family is a section of one of the subfunctors. -/
private theorem exists_labelled_refinement
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (I : Type v) (G : I → Subfunctor F)
    (hcover : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (iSup G).ι)
    {U : BigFppfOver B S hS} {R : Sieve U}
    (x : R.arrows.FamilyOfElements F) (hx : x.Compatible)
    (E : PreZeroHypercover.{u + 1} U) (hE : BigFppfOver.IsCovering B S hS ⟨U, E⟩)
    (hER : E.presieve₀ ≤ R) :
    ∃ E' : PreZeroHypercover.{u + 1} U,
      BigFppfOver.IsCovering B S hS ⟨U, E'⟩ ∧ E'.presieve₀ ≤ R ∧
      ∀ (a : E'.I₀) (ha : R (E'.f a)), ∃ i, ∃ t : (G i).toFunctor.obj (op (E'.X a)),
        (G i).ι.app (op (E'.X a)) t = x (Y := E'.X a) (E'.f a) ha := by
  classical
  have hmemE (j : E.I₀) : R (E.f j) := hER _ _ ⟨j⟩
  choose Rj hRj hloc using fun j ↦
    exists_local_iSup_section G hcover (E.X j) (x (Y := E.X j) (E.f j) (hmemE j))
  choose Fj hFj hFjR using fun j ↦
    exists_overCovering_refining_sieve B S hS (U := E.X j) (R := Rj j) (hRj j)
  have hEF : BigFppfOver.IsCovering B S hS ⟨U, E.bind Fj⟩ :=
    B.coverings_isSite.2.1 ⟨U.left, E.map (BigFppfOver.forget B S hS)⟩ hE
      (fun j ↦ ⟨(E.X j).left, (Fj j).map (BigFppfOver.forget B S hS)⟩) (fun j ↦ hFj j)
      fun _ ↦ rfl
  refine ⟨E.bind Fj, hEF, ?_, ?_⟩
  · rw [Presieve.ofArrows_le_iff]
    rintro ⟨j, k⟩
    exact R.downward_closed (hmemE j) ((Fj j).f k)
  · rintro ⟨j, k⟩ ha
    obtain ⟨i, t, ht⟩ := hloc j ((Fj j).f k) (hFjR j _ _ ⟨k⟩)
    refine ⟨i, t, ht.trans ?_⟩
    have ha' : R ((Fj j).f k ≫ E.f j) := by
      simpa [PreZeroHypercover.bind, PreZeroHypercover.pushforward] using ha
    symm
    calc x (Y := (Fj j).X k) ((Fj j).f k ≫ E.f j) ha' =
        F.map ((Fj j).f k).op (x (Y := E.X j) (E.f j) (hmemE j)) := by
          simpa using hx (g₁ := 𝟙 ((Fj j).X k)) (g₂ := (Fj j).f k)
            (f₁ := (Fj j).f k ≫ E.f j) (f₂ := E.f j) (h₁ := ha') (h₂ := hmemE j) (by simp)

/-! ### Amalgamating the descended sections -/

/-- A section of `G` over a member of a covering which maps to the corresponding member of a
compatible family takes the same value on two morphisms equalised by that member. -/
private theorem map_eq_map_of_comp_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (G : Subfunctor F) {U V : BigFppfOver B S hS}
    {R : Sieve U} {x : R.arrows.FamilyOfElements F} (hx : x.Compatible) {f : V ⟶ U} (hf : R f)
    (t : G.toFunctor.obj (op V)) (ht : G.ι.app (op V) t = x f hf)
    {Z : BigFppfOver B S hS} (p₁ p₂ : Z ⟶ V) (hp : p₁ ≫ f = p₂ ≫ f) :
    G.toFunctor.map p₁.op t = G.toFunctor.map p₂.op t := by
  apply injective_of_mono (G.ι.app (op Z))
  calc G.ι.app (op Z) (G.toFunctor.map p₁.op t) = F.map p₁.op (G.ι.app _ t) :=
        (G.ι.naturality_apply p₁.op t).symm
    _ = F.map p₁.op (x f hf) := by rw [ht]
    _ = F.map p₂.op (x f hf) :=
        hx (g₁ := p₁) (g₂ := p₂) (f₁ := f) (f₂ := f) (h₁ := hf) (h₂ := hf) hp
    _ = F.map p₂.op (G.ι.app _ t) := by rw [← ht]
    _ = G.ι.app (op Z) (G.toFunctor.map p₂.op t) := G.ι.naturality_apply p₂.op t

/-- A section of a representable subfunctor over `W a` descending the `a`-th member of a
compatible family restricts, along a morphism to `U` factoring through `W a`, to the member of
the family at that morphism. -/
private theorem map_descended_eq_of_comp_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (G : Subfunctor F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G.toFunctor)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS G.ι)
    {U : BigFppfOver B S hS} {R : Sieve U} {x : R.arrows.FamilyOfElements F} (hx : x.Compatible)
    {A : Type w} {V W : A → BigFppfOver B S hS} {π : ∀ a, V a ⟶ U} {ι : ∀ a, W a ⟶ U}
    {imageOpen : ∀ a, V a ⟶ W a} (a : A) (imageOpen_comp : imageOpen a ≫ ι a = π a)
    (hImageCover : Sieve.generate (Presieve.singleton (imageOpen a)) ∈
      BigFppfOver.topology B S hS (W a))
    (hmem : R (π a)) (descended : G.toFunctor.obj (op (W a)))
    (hd : F.map (imageOpen a).op (G.ι.app _ descended) = x (π a) hmem)
    {V' Z : BigFppfOver B S hS} (f : V' ⟶ U) (hf : R f) (p : Z ⟶ W a) (q : Z ⟶ V')
    (hpq : p ≫ ι a = q ≫ f) :
    F.map p.op (G.ι.app _ descended) = F.map q.op (x f hf) := by
  apply section_eq_of_locally_eq_to_representable_subfunctor B S hS F G hG hrep Z
    ((Sieve.generate (Presieve.singleton (imageOpen a))).pullback p)
    ((BigFppfOver.topology B S hS).pullback_stable p hImageCover) (G.toFunctor.map p.op descended)
  intro T g hg
  obtain ⟨Y, k, b, hb, hkb⟩ := hg
  cases hb
  change k ≫ imageOpen a = g ≫ p at hkb
  change F.map g.op (F.map p.op (G.ι.app _ descended)) = F.map g.op (F.map q.op (x f hf))
  calc F.map g.op (F.map p.op (G.ι.app _ descended)) =
        F.map (g ≫ p).op (G.ι.app _ descended) := by
        simp only [op_comp, Functor.map_comp, types_comp_apply]
    _ = F.map (k ≫ imageOpen a).op (G.ι.app _ descended) := by rw [hkb]
    _ = F.map k.op (x (π a) hmem) := by
        simp only [op_comp, Functor.map_comp, types_comp_apply, hd]
    _ = F.map (g ≫ q).op (x f hf) :=
        hx (g₁ := k) (g₂ := g ≫ q) (h₁ := hmem) (h₂ := hf) (by
          rw [← imageOpen_comp, ← Category.assoc, hkb, Category.assoc, hpq, ← Category.assoc])
    _ = F.map g.op (F.map q.op (x f hf)) := by simp

/-- An amalgamation of a compatible family restricts over `W a` to the section descended from
the `a`-th member of the family. -/
private theorem descended_eq_map_of_isAmalgamation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (G : Subfunctor F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G.toFunctor)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS G.ι)
    {U : BigFppfOver B S hS} {R : Sieve U} {x : R.arrows.FamilyOfElements F}
    {A : Type w} {V W : A → BigFppfOver B S hS} {π : ∀ a, V a ⟶ U} {ι : ∀ a, W a ⟶ U}
    {imageOpen : ∀ a, V a ⟶ W a} (a : A) (imageOpen_comp : imageOpen a ≫ ι a = π a)
    (hImageCover : Sieve.generate (Presieve.singleton (imageOpen a)) ∈
      BigFppfOver.topology B S hS (W a))
    (hmem : R (π a)) (descended : G.toFunctor.obj (op (W a)))
    (hd : F.map (imageOpen a).op (G.ι.app _ descended) = x (π a) hmem)
    {t : F.obj (op U)} (ht : x.IsAmalgamation t) :
    G.ι.app _ descended = F.map (ι a).op t := by
  apply section_eq_of_locally_eq_to_representable_subfunctor B S hS F G hG hrep _
    (Sieve.generate (Presieve.singleton (imageOpen a))) hImageCover descended
  intro Z g hg
  obtain ⟨Y, k, b, hb, hkb⟩ := hg
  cases hb
  change k ≫ imageOpen a = g at hkb
  rw [← hkb]
  calc F.map (k ≫ imageOpen a).op (G.ι.app _ descended) = F.map k.op (x (π a) hmem) := by
        simp only [op_comp, Functor.map_comp, types_comp_apply, hd]
    _ = F.map k.op (F.map (π a).op t) := by rw [ht (π a) hmem]
    _ = F.map (k ≫ imageOpen a).op (F.map (ι a).op t) := by
        simp only [← Functor.map_comp_apply, ← op_comp, Category.assoc, imageOpen_comp]

/-- A compatible family for a sieve on `U` has a unique amalgamation once it is presented by a
family of morphisms each of which factors through an open subobject of `U` over which the family
descends to a representable subfunctor, the open subobjects covering `U` for the Zariski
topology and each factorization being a one-element fppf covering. -/
private theorem existsUnique_amalgamation_of_image_sections
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (B.zariskiTopology.over (B.obj hS)) F)
    (I : Type v) (G : I → Subfunctor F)
    (hG : ∀ i, Presheaf.IsSheaf (BigFppfOver.topology B S hS) (G i).toFunctor)
    (hrep : ∀ i, IsRepresentableByAlgebraicSpaces B S hS (G i).ι)
    (U : BigFppfOver B S hS) (R : Sieve U)
    (x : R.arrows.FamilyOfElements F) (hx : x.Compatible)
    (A : Type w) (V W : A → BigFppfOver B S hS)
    (π : ∀ a, V a ⟶ U) (ι : ∀ a, W a ⟶ U) (imageOpen : ∀ a, V a ⟶ W a)
    (imageOpen_comp : ∀ a, imageOpen a ≫ ι a = π a)
    (hOmem : Sieve.generate (Presieve.ofArrows W ι) ∈ B.zariskiTopology.over (B.obj hS) U)
    (hImageCover : ∀ a, Sieve.generate (Presieve.singleton (imageOpen a)) ∈
      BigFppfOver.topology B S hS (W a))
    (hmem : ∀ a, R (π a)) (label : A → I)
    (descended : ∀ a, (G (label a)).toFunctor.obj (op (W a)))
    (hd : ∀ a, F.map (imageOpen a).op ((G (label a)).ι.app _ (descended a)) = x (π a) (hmem a)) :
    ∃! s, x.IsAmalgamation s := by
  classical
  let d (a : A) : F.obj (op (W a)) := (G (label a)).ι.app _ (descended a)
  have hd' (a : A) : F.map (imageOpen a).op (d a) = x (π a) (hmem a) := hd a
  have hmatch (a : A) {V' Z : BigFppfOver B S hS} (f : V' ⟶ U) (hf : R f)
      (p : Z ⟶ W a) (q : Z ⟶ V') (hpq : p ≫ ι a = q ≫ f) :
      F.map p.op (d a) = F.map q.op (x f hf) :=
    map_descended_eq_of_comp_eq B S hS F (G (label a)) (hG _) (hrep _) hx a (imageOpen_comp a)
      (hImageCover a) (hmem a) (descended a) (hd a) f hf p q hpq
  have hdcompat : Presieve.Arrows.Compatible F ι d := by
    intro a b Z p q hpq
    apply section_eq_of_locally_eq_to_representable_subfunctor B S hS F (G (label a))
      (hG (label a)) (hrep (label a)) Z
      ((Sieve.generate (Presieve.singleton (imageOpen b))).pullback q)
      ((BigFppfOver.topology B S hS).pullback_stable q (hImageCover b))
      ((G (label a)).toFunctor.map p.op (descended a))
    intro T g hg
    obtain ⟨Y, k, f, hf, hkf⟩ := hg
    cases hf
    change k ≫ imageOpen b = g ≫ q at hkf
    change F.map g.op (F.map p.op (d a)) = F.map g.op (F.map q.op (d b))
    calc F.map g.op (F.map p.op (d a)) = F.map (g ≫ p).op (d a) := by simp
      _ = F.map k.op (x (π b) (hmem b)) :=
          hmatch a (π b) (hmem b) (g ≫ p) k (by
            rw [Category.assoc, hpq, ← Category.assoc, ← hkf, Category.assoc, imageOpen_comp b])
      _ = F.map (k ≫ imageOpen b).op (d b) := by
          simp only [op_comp, Functor.map_comp, types_comp_apply, hd']
      _ = F.map g.op (F.map q.op (d b)) := by rw [hkf]; simp
  obtain ⟨s, hs, huniq⟩ := (Presieve.isSheafFor_arrows_iff F ι).1
    ((Presieve.isSheafFor_iff_generate _).2 (hF.isSheafFor _ hOmem)) d hdcompat
  refine ⟨s, ?_, ?_⟩
  · intro V' f hf
    apply (hF.isSheafFor _
      ((B.zariskiTopology.over (B.obj hS)).pullback_stable f hOmem)).isSeparatedFor.ext
    intro Z g hg
    obtain ⟨Y, p, b, hb, hpb⟩ := hg
    cases hb with
    | mk a =>
      change p ≫ ι a = g ≫ f at hpb
      calc F.map g.op (F.map f.op s) = F.map (g ≫ f).op s := by simp
        _ = F.map (p ≫ ι a).op s := by rw [hpb]
        _ = F.map p.op (d a) := by simp [hs]
        _ = F.map g.op (x f hf) := hmatch a f hf p g hpb
  · intro t ht
    exact huniq t fun a ↦ (descended_eq_map_of_isAmalgamation B S hS F (G (label a)) (hG _)
      (hrep _) a (imageOpen_comp a) (hImageCover a) (hmem a) (descended a) (hd a) ht).symm

/-! ### The gluing theorem -/

/-- **Stacks 07WE.** A Zariski sheaf on the big fppf site over `S` which is covered, locally for
the fppf topology, by fppf subsheaves whose inclusions are representable by algebraic spaces is
an fppf sheaf. -/
@[stacks 07WE]
theorem isSheaf_of_locallySurjective_representable_subfunctors
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (B.zariskiTopology.over (B.obj hS)) F)
    (I : Type v) (G : I → Subfunctor F)
    (hG : ∀ i, Presheaf.IsSheaf (BigFppfOver.topology B S hS) (G i).toFunctor)
    (hrep : ∀ i, IsRepresentableByAlgebraicSpaces B S hS (G i).ι)
    (hcover : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (iSup G).ι) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) F := by
  apply (isSheaf_iff_isSheaf_of_type (J := BigFppfOver.topology B S hS) F).2
  classical
  intro U R hR x hx
  obtain ⟨E, hE, hER⟩ := exists_overCovering_refining_sieve B S hS hR
  obtain ⟨E', hE', hE'R, hlabels⟩ :=
    exists_labelled_refinement B S hS F I G hcover x hx E hE hER
  obtain ⟨hsurj, hfp⟩ := isCovering_surjective_flat_locallyOfFinitePresentation B S hS hE'
  have hmem (a : E'.I₀) : R (E'.f a) := hE'R _ _ ⟨a⟩
  choose label localSection hlocal using fun a ↦ hlabels a (hmem a)
  -- the open subscheme of `U` cut out by the image of the `a`-th member
  let W (a : E'.I₀) : ((BigFppfOver.toScheme B S hS).obj U).Opens :=
    ⟨Set.range (B.inclusion.map (E'.f a).left), by
      have : Flat (B.inclusion.map (E'.f a).left) := (hfp a).1
      have : LocallyOfFinitePresentation (B.inclusion.map (E'.f a).left) := (hfp a).2
      exact (B.inclusion.map (E'.f a).left).isOpenMap.isOpen_range⟩
  have hOmem := openSubobject_sieve_mem_zariskiTopology_over B S hS U W hsurj
  let imageOpen (a : E'.I₀) := factorThroughOpenSubobject B S hS (E'.X a) U (E'.f a) (W a)
    (fun _ hz ↦ Set.mem_range.mpr hz)
  have imageOpen_comp (a : E'.I₀) :
      imageOpen a ≫ openSubobjectInclusion B S hS U (W a) = E'.f a :=
    factorThroughOpenSubobject_comp B S hS (E'.X a) U (E'.f a) (W a)
      (fun _ hz ↦ Set.mem_range.mpr hz)
  have hImageCover (a : E'.I₀) :
      Sieve.generate (Presieve.singleton (imageOpen a)) ∈
        BigFppfOver.topology B S hS (openSubobject B S hS U (W a)) :=
    singleton_factorThroughOpenSubobject_mem_topology B S hS (E'.f a) (W a) rfl (hfp a).1
      (hfp a).2 fun _ hz ↦ Set.mem_range.mpr hz
  choose descended hdesc using fun a ↦
    exists_section_of_sheaf_of_covering_singleton (hG (label a)) (imageOpen a) (hImageCover a)
      (localSection a) (by
        intro Z p₁ p₂ hp
        exact map_eq_map_of_comp_eq B S hS (G (label a)) hx (hmem a) (localSection a)
          (hlocal a) p₁ p₂ (by rw [← imageOpen_comp a, reassoc_of% hp]))
  refine existsUnique_amalgamation_of_image_sections B S hS F hF I G hG hrep U R x hx
    E'.I₀ E'.X (fun a ↦ openSubobject B S hS U (W a)) E'.f
    (fun a ↦ openSubobjectInclusion B S hS U (W a)) imageOpen imageOpen_comp hOmem hImageCover
    hmem label descended fun a ↦ ?_
  change (G (label a)).ι.app _
    ((G (label a)).toFunctor.map (imageOpen a).op (descended a)) = _
  rw [hdesc a]
  exact hlocal a

end AlgebraicGeometry.Space

end
