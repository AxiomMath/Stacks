module

public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveFlatFppfLocalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.FiniteCoproductsOfRepresentables
public import StacksFrontier.CategoryTheory.Sites.Topos.JointlyLocallyInhabited
public import StacksCore.Tactic.StacksAttribute

/-!
# An affine atlas object covers the final sheaf on the site of a quasi-compact stack

Let `𝒳` be a quasi-compact algebraic stack over a scheme `S` contained in a big fppf site `B`,
with one of the topologies of **Stacks 06TP** on its total category. This file produces a *single*
object `x` of that site lying over an affine scheme whose sheafified representable surjects onto
the final sheaf, that is, with `h_x^# ⟶ *` locally surjective.

That assertion is condition (1) of **Stacks 0GN4** for the collection `B` of the proof of
**Stacks 0GQV** — the objects of the site lying over affine schemes — in the case `m = 1`, which
is the case the source uses: it takes the single `x : U ⟶ 𝒳` with `U` affine and `x` surjective
smooth that quasi-compactness provides.

**Stacks 0GQV asserts its conclusion in two topologies, the fppf and the étale one, and this
condition is available in both.** The construction of `x` is the same, and so is the passage from
a covering sieve downstairs to a covering family upstairs; the two differ only in which tag reads
the sections of the affine smooth presentation off a covering of the base. For the fppf topology
that is **Stacks 06QA**, which asks the 1-morphism to be surjective, flat and locally of finite
presentation; for the étale topology it is **Stacks 06XH** part (2), which asks it to be
surjective and smooth. Stacks 04YC supplies a surjective smooth presentation, so both apply, and
everything else is proved once, at an arbitrary topology, in
`AlgebraicGeometry.Stack.exists_isAffineObject_cover_nonempty_hom_associatedTopology`.

## Main results

* `AlgebraicGeometry.Stack.exists_isAffineObject_cover_nonempty_hom_associatedTopology`: every
  object of the site of Stacks 06TP at a topology in which a surjective smooth 1-morphism admits
  fibre lifts is covered by objects admitting a morphism to one fixed object lying over an affine
  scheme.
* `AlgebraicGeometry.Stack.exists_isAffineObject_cover_nonempty_hom` and
  `AlgebraicGeometry.Stack.exists_isAffineObject_cover_nonempty_hom_etale`: its fppf and étale
  instances.
* `AlgebraicGeometry.Stack`
  `.exists_isAffineObject_isLocallySurjective_terminal_from_associatedTopology`: the same read as
  local surjectivity of `h_x^# ⟶ *`, which is condition (1) of Stacks 0GN4 at `m = 1`.
* `AlgebraicGeometry.Stack.exists_isAffineObject_isLocallySurjective_terminal_from` and
  `AlgebraicGeometry.Stack.exists_isAffineObject_isLocallySurjective_terminal_from_etale`:
  condition (1) for the fppf and for the étale site of Stacks 0GQV.

## Implementation notes

Quasi-compactness enters once, through
`AlgebraicGeometry.Stack.isQuasiCompactStack_iff_hasAffineSmoothPresentation` (**Stacks 04YC**,
parts (1) and (2)): it gives an *affine* object `U₀` of the big fppf category over `S` and a
surjective, relatively smooth 1-morphism `f` from the category it represents to `𝒳`. The object
taken is `x = f(1_{U₀})`, the image of the terminal object of the slice `(Sch/S)/U₀`. It lies
over `U₀`, hence over an affine scheme, because `f` is a based functor: its structural equality
`CategoryTheory.BasedFunctor.w` identifies the projection of `f(a)` with the projection of `a`,
which for `a = 1_{U₀}` is `U₀` itself.

That every object is covered by objects mapping to `x` is the fibre-lifting hypothesis applied to
`f`: **Stacks 06QA**, `AlgebraicGeometry.Stack.exists_fppfCovering_fibre_lift`, in the fppf case,
and **Stacks 06XH** part (2), `AlgebraicGeometry.Stack.exists_etaleCovering_fibre_lift`, in the
étale case. The fppf one asks for flatness
and local finite presentation of `f`, which relative smoothness supplies in two steps: the
relative property of **Stacks 03YK** gives the existential smooth-diagram test of **Stacks 06FM**
by `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty`, which is
smoothness of a 1-morphism of algebraic stacks in the sense of **Stacks 075U**, and smoothness
implies flatness and local finite presentation by
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isSmooth` and
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth`
(**Stacks 0DNP**). Surjectivity is used in the form **Stacks 04ZS** asks for, surjectivity on
points, which is what Stacks 04YC produces.

Either tag produces a covering sieve *downstairs*, of the scheme `z` lies over, together with a
lift of `z` over each of its members. The family of those lifts is a covering family of `z`
upstairs: in a category fibred in groupoids every morphism is strongly cartesian over its image,
and the images of the lifts generate the given sieve downstairs — each one equals its member of
the sieve after the comparison isomorphism of `CategoryTheory.Functor.IsHomLift.domain_eq`, so
the generated sieve contains it. Each lift has a morphism to `x`: its source is `f(a)` for an
object `a` of the slice over `U₀`, and the structure morphism of `a` is a morphism
`a ⟶ 1_{U₀}` of the slice.

The passage from the covering to local surjectivity of `h_x^# ⟶ *` needs only that the final
sheaf has at most one section over any object, which is
`Stacks.Topos.subsingleton_terminal_sections`: the condition that a lifted section map to the
given one is then vacuous, and a section of `h_x^#` over an object admitting a morphism to `x` is
the one `CategoryTheory.Sheaf.sectionEquiv` attaches to that morphism.

## References

* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 06NU](https://stacks.math.columbia.edu/tag/06NU)
* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 0DNP](https://stacks.math.columbia.edu/tag/0DNP)
* [Stacks Project, Tag 0GN4](https://stacks.math.columbia.edu/tag/0GN4)
* [Stacks Project, Tag 0GQV](https://stacks.math.columbia.edu/tag/0GQV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe w₁ v₁ u₁

/-- A sheaf of sets surjects onto the final sheaf as soon as every object of the site carries a
covering sieve over whose members the sheaf has a section.

This is the converse of `Stacks.Sites.QuasiCompactCriterion.exists_covering_nonempty_section`, and
like it uses only that the final sheaf has at most one section over any object, so that the
condition on the lifted section is vacuous. -/
private theorem isLocallySurjective_terminal_from_of_exists_covering_section
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {G : Sheaf J (Type w₁)}
    (h : ∀ U : C, ∃ T ∈ J U, ∀ ⦃V : C⦄ (g : V ⟶ U), T.arrows g →
      Nonempty (G.obj.obj (op V))) :
    Sheaf.IsLocallySurjective (terminal.from G) := by
  refine ⟨fun {U} _ => ?_⟩
  obtain ⟨T, hT, hsec⟩ := h U
  refine J.superset_covering (fun V g hg => ?_) hT
  obtain ⟨t⟩ := hsec g hg
  exact ⟨t, (Stacks.Topos.subsingleton_terminal_sections J (op V)).elim _ _⟩

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Every object of the site of Stacks 06TP at a topology in which a surjective smooth
1-morphism admits fibre lifts is covered by objects admitting a morphism to one fixed object lying
over an affine scheme**, for a quasi-compact algebraic stack.

The object is `f(1_{U₀})` for an affine smooth presentation `f` by `U₀` of **Stacks 04YC**, and
the covering is the one the hypothesis `h_lift` produces for `f`; see the module documentation.

The hypothesis is the fibre-lifting property in the topology `τ` localized at `S`, asked of a
surjective *smooth* 1-morphism, which is all Stacks 04YC produces. Its two instances are
**Stacks 06QA** for the fppf topology, which asks instead for flatness and local finite
presentation — both implied by smoothness — and **Stacks 06XH** part (2) for the étale topology,
which asks for smoothness on the nose. Nothing else in the proof refers to the topology: the
covering family upstairs is built from the covering sieve downstairs by the fibredness of `𝒳`
alone. -/
theorem exists_isAffineObject_cover_nonempty_hom_associatedTopology
    (τ : GrothendieckTopology B.Schemes)
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h_lift : ∀ (𝒵 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒳),
      IsSurjective B S hS f → AlgebraicStacks.IsSmooth B S hS f →
      ∀ (U : BigFppfOver B S hS) (y : 𝒳.val.val.p.Fiber U),
        ∃ R ∈ τ.over (B.obj hS) U,
          ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
            ∃ (x : 𝒵.val.val.obj)
              (α : (CatFiberedInGroupoids.homFunctor f.hom).obj x ⟶ y.1),
              𝒳.val.val.p.IsHomLift k α) :
    ∃ x : 𝒳.val.val.obj, IsAffineObject B S hS 𝒳.val.val.p x ∧
      ∀ z : 𝒳.val.val.obj, ∃ T ∈ associatedTopology B S hS 𝒳.val.val.p τ z,
        ∀ ⦃y : 𝒳.val.val.obj⦄ (g : y ⟶ z), T.arrows g → Nonempty (y ⟶ x) := by
  classical
  obtain ⟨U₀, hU₀, f, hsurj, hsmooth⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒳).1 hqc
  obtain ⟨hfrep, hrel⟩ := hsmooth
  have hsm : AlgebraicStacks.IsSmooth B S hS f :=
    hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ h => Space.IsSmooth B S hS h) 𝒳.property f.hom hfrep hrel
  let F := CatFiberedInGroupoids.homFunctor f.hom
  have hw : F ⋙ 𝒳.val.val.p = (schemeFibredCategory B S hS U₀).val.p := f.hom.hom.w
  refine ⟨F.obj (Over.mk (𝟙 U₀)), ?_, ?_⟩
  · have hproj : 𝒳.val.val.p.obj (F.obj (Over.mk (𝟙 U₀))) = U₀ :=
      Functor.congr_obj hw (Over.mk (𝟙 U₀))
    change IsAffine ((BigFppfOver.toScheme B S hS).obj
      (𝒳.val.val.p.obj (F.obj (Over.mk (𝟙 U₀)))))
    rwa [hproj]
  · intro z
    obtain ⟨R, hR, hlift⟩ := h_lift _ f hsurj hsm
      (𝒳.val.val.p.obj z) (Functor.Fiber.mk (a := z) rfl)
    have hch : ∀ i : Σ V : BigFppfOver B S hS, {k : V ⟶ 𝒳.val.val.p.obj z // R.arrows k},
        ∃ (a : (schemeFibredCategory B S hS U₀).val.obj) (φ : F.obj a ⟶ z),
          𝒳.val.val.p.IsHomLift i.2.1 φ := fun i => hlift i.2.2
    choose a φ hφ using hch
    refine ⟨Sieve.ofArrows (fun i => F.obj (a i)) φ, ?_, ?_⟩
    · rw [associatedTopology, Functor.inheritedTopology_eq]
      refine Precoverage.generate_mem_toGrothendieck
        ⟨fun _ q _ => Functor.IsFiberedInGroupoids.isStronglyCartesian
          𝒳.val.isFiberedInGroupoids q, ?_⟩
      rw [GrothendieckTopology.mem_toPrecoverage_iff, Presieve.map_ofArrows]
      refine (τ.over (B.obj hS)).superset_covering (fun V k hk => ?_) hR
      let i : Σ V' : BigFppfOver B S hS, {k' : V' ⟶ 𝒳.val.val.p.obj z // R.arrows k'} :=
        ⟨V, k, hk⟩
      have hinst := hφ i
      have hdom : 𝒳.val.val.p.obj (F.obj (a i)) = V :=
        IsHomLift.domain_eq 𝒳.val.val.p k (φ i)
      have hfac : 𝒳.val.val.p.map (φ i) = eqToHom hdom ≫ k := by
        simpa using IsHomLift.fac' 𝒳.val.val.p k (φ i)
      refine ⟨𝒳.val.val.p.obj (F.obj (a i)), eqToHom hdom.symm, 𝒳.val.val.p.map (φ i),
        Presieve.ofArrows.mk i, ?_⟩
      rw [hfac, eqToHom_trans_assoc]
      simp
    · intro y g hg
      obtain ⟨i, c, hc⟩ :=
        (Sieve.mem_ofArrows_iff (fun i => F.obj (a i)) φ g).1 hg
      exact ⟨c ≫ F.map (Over.homMk (a i).hom (Category.comp_id (a i).hom))⟩

/-- Fibre lifts for a surjective smooth 1-morphism over an fppf covering of the base, by Stacks 06QA
and the fact that smooth 1-morphisms are flat and locally of finite presentation. -/
private theorem exists_fppfCovering_fibre_lift_of_isSmooth
    {𝒵 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒵 ⟶ 𝒴) (hsurj : IsSurjective B S hS f)
    (hsm : AlgebraicStacks.IsSmooth B S hS f) (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U) :
    ∃ R ∈ B.topology.over (B.obj hS) U,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
        ∃ (x : 𝒵.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj x ⟶ y.1),
          𝒴.val.val.p.IsHomLift k α :=
  exists_fppfCovering_fibre_lift B S hS f hsurj
    (AlgebraicStacks.isFlat_of_isSmooth B S hS f hsm)
    (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS f hsm) U y

/-- **Every object of the fppf site of a quasi-compact algebraic stack is covered by objects
admitting a morphism to one fixed object lying over an affine scheme.**

This is
`AlgebraicGeometry.Stack.exists_isAffineObject_cover_nonempty_hom_associatedTopology` at the big
fppf topology, its fibre-lifting hypothesis discharged by **Stacks 06QA**,
`AlgebraicGeometry.Stack.exists_fppfCovering_fibre_lift`: flatness and local finite presentation
of the presentation, which that tag asks for, follow from its smoothness by
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isSmooth` and
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth`
(**Stacks 0DNP**). -/
theorem exists_isAffineObject_cover_nonempty_hom
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property) :
    ∃ x : 𝒳.val.val.obj, IsAffineObject B S hS 𝒳.val.val.p x ∧
      ∀ z : 𝒳.val.val.obj, ∃ T ∈ fppfTopology B S hS 𝒳.val z,
        ∀ ⦃y : 𝒳.val.val.obj⦄ (g : y ⟶ z), T.arrows g → Nonempty (y ⟶ x) :=
  exists_isAffineObject_cover_nonempty_hom_associatedTopology B S hS 𝒳 B.topology hqc
    fun _ f => exists_fppfCovering_fibre_lift_of_isSmooth B S hS f

/-- **Every object of the étale site of a quasi-compact algebraic stack is covered by objects
admitting a morphism to one fixed object lying over an affine scheme.**

This is
`AlgebraicGeometry.Stack.exists_isAffineObject_cover_nonempty_hom_associatedTopology` at the big
étale topology, its fibre-lifting hypothesis discharged by **Stacks 06XH** part (2),
`AlgebraicGeometry.Stack.exists_etaleCovering_fibre_lift`, which reads the fibre lifts of a
surjective smooth 1-morphism off an *étale* covering of the base. The affine smooth presentation
of **Stacks 04YC** is smooth and surjective, which is exactly what that tag asks for, so this
needs nothing of the presentation beyond what the fppf case needs. -/
theorem exists_isAffineObject_cover_nonempty_hom_etale
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property) :
    ∃ x : 𝒳.val.val.obj, IsAffineObject B S hS 𝒳.val.val.p x ∧
      ∀ z : 𝒳.val.val.obj,
        ∃ T ∈ associatedTopology B S hS 𝒳.val.val.p (etaleTopology B) z,
          ∀ ⦃y : 𝒳.val.val.obj⦄ (g : y ⟶ z), T.arrows g → Nonempty (y ⟶ x) :=
  exists_isAffineObject_cover_nonempty_hom_associatedTopology B S hS 𝒳 (etaleTopology B) hqc
    fun _ f hsurj hsm => exists_etaleCovering_fibre_lift B S hS f hsurj hsm

/-- **The affine atlas object covers the final object of the fppf site of a quasi-compact
algebraic stack.** The object produced by
`AlgebraicGeometry.Stack.exists_isAffineObject_cover_nonempty_hom`, read as a one-element
covering family of the final object in the sense of
`CategoryTheory.GrothendieckTopology.CoversTop`.

The two statements say the same thing: an arrow of `CategoryTheory.Sieve.ofObjects` at a
one-element family is an arrow whose source admits a morphism to the single member, which is
exactly what the covering sieve of the other statement provides. `CoversTop` is the site-level
form, so unlike the sheaf-level condition (1) it transports along an equivalence of sites across
a universe gap, by `CategoryTheory.GrothendieckTopology.coversTop_inverse_obj`. -/
theorem exists_isAffineObject_coversTop
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property) :
    ∃ x : 𝒳.val.val.obj, IsAffineObject B S hS 𝒳.val.val.p x ∧
      (fppfTopology B S hS 𝒳.val).CoversTop fun _ : PUnit.{u + 2} => x := by
  obtain ⟨x, hxaff, hcover⟩ := exists_isAffineObject_cover_nonempty_hom B S hS 𝒳 hqc
  refine ⟨x, hxaff, fun z => ?_⟩
  obtain ⟨T, hT, hhom⟩ := hcover z
  exact (fppfTopology B S hS 𝒳.val).superset_covering
    (fun _ g hg => (Sieve.mem_ofObjects_iff _ g).2 ⟨PUnit.unit, hhom g hg⟩) hT

/-- **Condition (1) of Stacks 0GN4 for the site of Stacks 06TP at a topology in which a surjective
smooth 1-morphism admits fibre lifts, with one object**, for a quasi-compact algebraic stack.
There is an object `x` of the site lying over an affine scheme for which the sheafification
`h_x^#` of its representable surjects onto the final sheaf.

This is what the proof of **Stacks 0GQV** uses at that point: the collection `B` of that proof is
the objects of the site lying over affine schemes, and the finite family of condition (1) is taken
to be the single object attached by **Stacks 04YC** to an affine smooth presentation. The
covering of every object by objects mapping to `x` is
`AlgebraicGeometry.Stack.exists_isAffineObject_cover_nonempty_hom_associatedTopology`; a morphism
of the site into `x` names a section of `h_x^#`, and the final sheaf has at most one section over
any object, so the covering is exactly local surjectivity of `h_x^# ⟶ *`. -/
theorem exists_isAffineObject_isLocallySurjective_terminal_from_associatedTopology
    (τ : GrothendieckTopology B.Schemes)
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property)
    (h_lift : ∀ (𝒵 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒳),
      IsSurjective B S hS f → AlgebraicStacks.IsSmooth B S hS f →
      ∀ (U : BigFppfOver B S hS) (y : 𝒳.val.val.p.Fiber U),
        ∃ R ∈ τ.over (B.obj hS) U,
          ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
            ∃ (x : 𝒵.val.val.obj)
              (α : (CatFiberedInGroupoids.homFunctor f.hom).obj x ⟶ y.1),
              𝒳.val.val.p.IsHomLift k α) :
    ∃ x : 𝒳.val.val.obj, IsAffineObject B S hS 𝒳.val.val.p x ∧
      Sheaf.IsLocallySurjective (terminal.from
        ((Sheaf.sheafifiedYoneda (associatedTopology B S hS 𝒳.val.val.p τ)).obj x)) := by
  obtain ⟨x, hxaff, hcover⟩ :=
    exists_isAffineObject_cover_nonempty_hom_associatedTopology B S hS 𝒳 τ hqc h_lift
  refine ⟨x, hxaff, isLocallySurjective_terminal_from_of_exists_covering_section fun z => ?_⟩
  obtain ⟨T, hT, hhom⟩ := hcover z
  refine ⟨T, hT, fun V g hg => ?_⟩
  obtain ⟨m⟩ := hhom g hg
  exact ⟨Sheaf.sectionEquiv (associatedTopology B S hS 𝒳.val.val.p τ)
    ((Sheaf.sheafifiedYoneda (associatedTopology B S hS 𝒳.val.val.p τ)).map m)⟩

/-- **Condition (1) of Stacks 0GN4 for the fppf site of a quasi-compact algebraic stack, with one
object.** There is an object `x` of the site lying over an affine scheme for which the
sheafification `h_x^#` of its representable surjects onto the final sheaf.

This is `exists_isAffineObject_isLocallySurjective_terminal_from_associatedTopology` at the big
fppf topology, with **Stacks 06QA** for the fibre lifts as in
`AlgebraicGeometry.Stack.exists_isAffineObject_cover_nonempty_hom`. -/
@[stacks 0GQV "condition (1) of Stacks 0GN4 for the fppf site, from Stacks 04YC and Stacks 06QA"]
theorem exists_isAffineObject_isLocallySurjective_terminal_from
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property) :
    ∃ x : 𝒳.val.val.obj, IsAffineObject B S hS 𝒳.val.val.p x ∧
      Sheaf.IsLocallySurjective (terminal.from
        ((Sheaf.sheafifiedYoneda (fppfTopology B S hS 𝒳.val)).obj x)) :=
  exists_isAffineObject_isLocallySurjective_terminal_from_associatedTopology B S hS 𝒳
    B.topology hqc
    fun _ f => exists_fppfCovering_fibre_lift_of_isSmooth B S hS f

/-- **Condition (1) of Stacks 0GN4 for the étale site of a quasi-compact algebraic stack, with one
object.** There is an object `x` of the site lying over an affine scheme for which the
sheafification `h_x^#` of its representable surjects onto the final sheaf in the étale topology.

This is the first of the four conditions the proof of **Stacks 0GQV** checks, for the second of
the two topologies the source asserts the tag in. It is
`exists_isAffineObject_isLocallySurjective_terminal_from_associatedTopology` at the big étale
topology, with **Stacks 06XH** part (2) for the fibre lifts as in
`AlgebraicGeometry.Stack.exists_isAffineObject_cover_nonempty_hom_etale`.

The source checks this condition by saying that the affine smooth surjection of Stacks 04YC makes
`h_x^# ⟶ *` an epimorphism of sheaves on `𝒳_τ`, which for `τ` the étale topology is the assertion
that a surjective smooth 1-morphism has sections étale-locally. That is Stacks 06XH part (2), and
it is the only place the étale proof of this condition differs from the fppf one. -/
@[stacks 0GQV "condition (1) of Stacks 0GN4 for the étale site, from Stacks 04YC and Stacks 06XH \
part (2)"]
theorem exists_isAffineObject_isLocallySurjective_terminal_from_etale
    (hqc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property) :
    ∃ x : 𝒳.val.val.obj, IsAffineObject B S hS 𝒳.val.val.p x ∧
      Sheaf.IsLocallySurjective (terminal.from
        ((Sheaf.sheafifiedYoneda
          (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).obj x)) :=
  exists_isAffineObject_isLocallySurjective_terminal_from_associatedTopology B S hS 𝒳
    (etaleTopology B) hqc
    fun _ f hsurj hsm => exists_etaleCovering_fibre_lift B S hS f hsurj hsm

end AlgebraicGeometry.Stack

end
