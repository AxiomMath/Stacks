module

public import Mathlib.CategoryTheory.Limits.Types.Coequalizers
public import Mathlib.CategoryTheory.Limits.Elements
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.Point.Basic
public import StacksFrontier.CategoryTheory.Sites.Point.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Points of sites and their topoi, and the properties of `p_*`

A point `Φ` of a site `(C, J)` — Mathlib's `CategoryTheory.GrothendieckTopology.Point` —
carries a stalk functor `Φ.sheafFiber : Sh(C) ⥤ Set` and a skyscraper functor
`Φ.skyscraperSheafFunctor : Set ⥤ Sh(C)`, and these are adjoint. Since the stalk functor is
moreover left exact (`Point.sheafFiber_leftExact`, i.e. Stacks 00Y5 (3) for Mathlib's notion
of a point), the pair is a morphism of topoi `Sh(pt) → Sh(C)`, i.e. a point of the topos in
the sense of Stacks 00Y4. Conversely, every point `p` of the topos comes from the point of
the site whose fiber functor is `U ↦ p⁻¹(h_U^#)`.

## Main definitions

* `CategoryTheory.GrothendieckTopology.Point.pointOfTopos`: the point of the topos
  associated to a point of the site (Stacks 00YA (1)).
* `CategoryTheory.GrothendieckTopology.Point.sheafFiberComparison`: the canonical
  comparison from the stalk functor, sending a germ represented by `(U, x, σ)` to
  the image of `x` under the map induced by `σ : h_U^# ⟶ F` (Stacks 00YA (2)).

## Main results

* `PointOfTopos.exists_sitePoint_fiber_eq`: the functor `U ↦ p⁻¹(h_U^#)` is, on the nose, the
  fiber functor of a site point (Stacks 00YA (2)).
* `PointOfTopos.isIso_sheafFiberComparison`: the canonical comparison identifies the
  reconstructed stalk functor with `p.inverseImage` (Stacks 00YA (2)).
* `PointOfTopos.isIso_conjugate_sheafFiberComparison`: the adjoint mate of that comparison
  identifies `p.pushforward` with the reconstructed skyscraper functor (Stacks 00YA (2)).

### Stacks 05UY

Stacks 05UY lists eight properties of `p_* : Set ⥤ Sh(C)` for `p` a point of the topos
`Sh(C)`. Seven of them are proved here, for an arbitrary point of an arbitrary topos, in the
form `PointOfTopos.*_pushforward`:

1. it commutes with arbitrary limits (`preservesLimitsOfSize_pushforward`);
2. it is left exact (`preservesFiniteLimits_pushforward`);
3. it is faithful (`faithful_pushforward`);
4. it transforms surjections into surjections (`preservesEpimorphisms_pushforward`);
5. it reflects injections (`reflectsMonomorphisms_pushforward`);
6. it reflects surjections (`reflectsEpimorphisms_pushforward`);
7. it reflects isomorphisms (`reflectsIsomorphisms_pushforward`).

As in `StacksFrontier/CategoryTheory/Sites/Subtopos/ClosedImmersion.lean`, "injection", "surjection"
and "isomorphism" of
sheaves are rendered as monomorphism, epimorphism and isomorphism.

## Implementation notes

In Stacks 00YA (2), equality of points of the topos is expressed by the canonical
comparison isomorphism of inverse image functors and its adjoint mate on pushforwards.
The comparison is defined for any functor on sheaves and any natural transformation on
the fiber functors; `sheafFiberComparison_toPresheafFiber` gives its formula on germs.
For a topos point and an isomorphism of fiber functors, the comparison and its mate are
isomorphisms. Thus the identifications respect the given adjunctions, rather than merely
identifying their underlying functors independently. The reconstruction uses
`Sheaf.sheafifiedYoneda`, whose sheaves take values in `Type (max u v)` for a category
with object universe `u` and morphism universe `v`. Thus both universes of the site remain
arbitrary, and the category of elements of the reconstructed fiber is small in the
universe of sets. No smallness restriction is added to the forward construction.

The comparison is built first on the composite `sheafToPresheaf J _ ⋙ Φ.presheafFiber`, as
`Point.presheafFiberComparison`, and only then transported to `Φ.sheafFiber`, which is that
composite by definition. On the composite every object in sight has the form
`Φ.presheafFiber.obj G.obj`, so the colimit lemmas for `Point.presheafFiberDesc` apply
without any unfolding of `Point.sheafFiber`.

Properties 1 and 2 hold because `p_*` is a right adjoint. The remaining five rest on the fact
that the counit `ε_E : p^{-1}p_*E → E` is a *split* surjection, which is `counitSection`
below: `p^{-1}` and `p_*` both preserve the terminal object (the first because it is left
exact, the second because it is a right adjoint), so `p^{-1}p_*(pt)` has a unique element
`basePoint`, and `e ↦ p^{-1}p_*(pt ↦ e)(basePoint)` is a natural section of `ε`. Property 4
is separate: every epimorphism of `Type w` is *split*, and a split epimorphism is preserved by
any functor whatsoever.

### The eighth property of Stacks 05UY is false

The remaining assertion of Stacks 05UY is that `p_*` commutes with coequalizers. That is
false, and no declaration below claims it.

The failure is proved here in the form
`Point.subsingleton_fiber_of_preservesCoequalizers`: if the skyscraper presheaf functor
`E ↦ u^pE` of a point of a site commutes with coequalizers, then every `u(X)` is a
subsingleton. Its engine is `Point.not_preservesCoequalizers_coyoneda`, which says that
`Map(A, -) : Set ⥤ Set` does not preserve coequalizers once `A` has two elements, and the
identification `u^pE(X) = Map(u(X), E)` of Stacks 04EI, which is
`Point.skyscraperPresheafIsoYoneda`. Together these locate the error precisely at the step
"it follows immediately from this formula" of the Stacks proof: from
`p_*E(U) = Mor(u(U), E)` one gets that `p_*` transforms surjections into surjections, but not
that it transforms coequalizers into coequalizers.

Spelled out as a counterexample to the clause as stated for `p_* : Set ⥤ Sh(C)`:

Take `C = WalkingParallelPair`, with objects `zero`, `one` and the two distinct morphisms
`left, right : zero ⟶ one`, and take `J = ⊥`, so that `Sh(C, J)` is the category of
presheaves on `C` (`sheafBotEquivalence`). Let `Φ = pointBot zero` be the point of `(C, ⊥)`
attached to `zero` (Mathlib's `GrothendieckTopology.pointBot`), whose fibre functor is
`u = Hom(zero, -)`; so `u(zero)` is a singleton and `u(one) = {left, right}` has two
elements, and `p^{-1}` is evaluation at `zero` (`pointBotPresheafFiberIso`). Then
`p_*E(V) = Map(u(V), E)`, so `p_*E(zero) = E` and `p_*E(one) = E × E`, the two restriction
maps `p_*E(one) → p_*E(zero)` being the two projections.

Let `α, β : PUnit ⇉ Bool` be the two maps `pt ↦ true` and `pt ↦ false`. Their coequalizer in
`Type` is `PUnit`, and `p_*PUnit` is the terminal presheaf. If `p_*` commuted with
coequalizers then `p_*Bool → p_*PUnit` would be a coequalizer of `p_*α, p_*β`, so every map
out of `p_*Bool` equalizing `p_*α` and `p_*β` would factor through a terminal object. It does
not. Let `F` be the presheaf with `F(zero) = PUnit`, `F(one) = Bool` and both restriction maps
`F(one) → F(zero)` the unique map to `PUnit` (a presheaf, since `Hom(one, zero)` is empty and
`Hom(one, one)` and `Hom(zero, zero)` are trivial), and let `h : p_*Bool ⟶ F` be
`h_zero = (unique map to PUnit)` and `h_one : Bool × Bool → Bool`, `(a, b) ↦ decide (a = b)`.
Naturality is automatic because every component of `F` other than at `one` is `PUnit`. Now
`p_*α` and `p_*β` send the unique element of `p_*PUnit(one)` to `(true, true)` and
`(false, false)`, and `h_one` takes the value `true` at both, so `h` does equalize `p_*α` and
`p_*β`; but `h_one (true, true) = true ≠ false = h_one (true, false)`, so `h_one` is not
constant and `h` does not factor through the terminal presheaf.

The gap in the Stacks proof is the step "it follows immediately from this formula", applied to
`p_*E(U) = Map(u(U), E)`: the functor `Map(A, -) : Set ⥤ Set` does preserve surjections, but
it does not preserve coequalizers as soon as `A` has more than one element. What is true —
and what the applications use — is that `Map(A, -)` preserves quotients by *equivalence
relations*, i.e. `p_*` preserves the coequalizer of a pair which is an equivalence relation on
its target. That corrected statement is not proved here either.

### Relation to Stacks 04EL

`Point.skyscraperPresheafIsoYoneda` is also the computation that the Stacks proof of 04EL (3)
performs: with `S` the site of sets and `i : Sh(pt) → Sh(S)` the equivalence sending `E` to
the sheaf `V ↦ Mor(V, E) = (yoneda.obj E)`, it says `f_*i_*E = u^*(yoneda.obj E) = p_*E`. The
remaining clauses of 04EL are not proved here: Mathlib's `Functor.IsContinuous J K` for
`u : C ⥤ D` forces the sheaves to be valued in `Type (max u₁ v₁ u₂ v₂)`, which for
`D = Type w` is `Type (max u v (w+1))` and not `Type w`, so it cannot be applied to a
`Type w`-valued fibre functor. That is exactly why Stacks takes `S` to be the *powerset* of an
infinite set rather than all sets — and the equivalence `Sh(S) ≃ Sets` for such a small `S`
(Stacks 00XD) is not in Mathlib, which proves it for the site of all types
(`CategoryTheory.typeEquiv`).

## References

* [Stacks Project, Tag 00YA](https://stacks.math.columbia.edu/tag/00YA)
* [Stacks Project, Tag 05UY](https://stacks.math.columbia.edu/tag/05UY)
* [Stacks Project, Tag 04EL](https://stacks.math.columbia.edu/tag/04EL)
-/

@[expose] public section

open CategoryTheory Limits
universe w₁ w₂ w v u

namespace PointOfTopos

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (p : PointOfTopos.{w, v, u} J)

/-! ### The counit of a point of a topos is a split surjection -/

/-- `p_*` of a one-point set is a terminal object of the topos: `p_*` is a right adjoint, and
the adjunction identifies maps into `p_*(pt)` with maps into `pt`. -/
noncomputable def isTerminalPushforwardObjPUnit :
    IsTerminal (p.pushforward.obj (PUnit.{w + 1} : Type w)) := by
  haveI h : ∀ F : Sheaf J (Type w), Unique (F ⟶ p.pushforward.obj (PUnit.{w + 1} : Type w)) :=
    fun F =>
      haveI : Unique (p.inverseImage.obj F ⟶ (PUnit.{w + 1} : Type w)) :=
      ⟨⟨Limits.Types.isTerminalPUnit.from _⟩, fun _ => Limits.Types.isTerminalPUnit.hom_ext _ _⟩
      (p.adj.homEquiv F (PUnit.{w + 1} : Type w)).symm.unique
  exact IsTerminal.ofUnique _

/-- `p^{-1}p_*` of a one-point set is a one-point set: `p_*` preserves the terminal object
because it is a right adjoint, and `p^{-1}` preserves it because it is left exact. -/
noncomputable def isTerminalInverseImagePushforwardObjPUnit :
    IsTerminal ((p.pushforward ⋙ p.inverseImage).obj (PUnit.{w + 1} : Type w)) :=
  haveI := p.preservesFiniteLimits
  p.isTerminalPushforwardObjPUnit.isTerminalObj p.inverseImage _

/-- The unique element of the one-point set `p^{-1}p_*(pt)`. -/
noncomputable def basePoint : (p.pushforward ⋙ p.inverseImage).obj (PUnit.{w + 1} : Type w) :=
  (Limits.Types.isTerminalEquivUnique _ p.isTerminalInverseImagePushforwardObjPUnit).default

/-- The canonical natural section of the counit `ε : p^{-1}p_* ⟹ 1` of a point of a topos: an
element `e` of a set `E` is a map `pt → E`, and `p^{-1}p_*` of that map takes the unique
element of `p^{-1}p_*(pt)` to an element of `p^{-1}p_*E` above `e`. -/
noncomputable def counitSection : 𝟭 (Type w) ⟶ p.pushforward ⋙ p.inverseImage where
  app E :=
    ↾fun e => (p.pushforward ⋙ p.inverseImage).map (↾fun (_ : PUnit.{w + 1}) => e) p.basePoint
  naturality E E' g := by
    ext e
    have h : (↾fun (_ : PUnit.{w + 1}) => e) ≫ g = ↾fun (_ : PUnit.{w + 1}) => g e := by
      ext; rfl
    dsimp only [Functor.comp_obj, Functor.id_obj, Functor.id_map, Functor.comp_map,
      TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
    rw [← h, Functor.map_comp, Functor.map_comp, types_comp_apply]

/-- `counitSection` is a section of the counit: `ε_E` is a split surjection. -/
theorem counit_app_counitSection_app (E : Type w) (e : E) :
    p.adj.counit.app E (p.counitSection.app E e) = e :=
  ConcreteCategory.congr_hom (p.adj.counit.naturality (↾fun (_ : PUnit.{w + 1}) => e)) p.basePoint

/-- The counit `ε_E : p^{-1}p_*E → E` of a point of a topos is a split epimorphism, a section
being given by `counitSection`. -/
instance isSplitEpi_counit_app (E : Type w) : IsSplitEpi (p.adj.counit.app E) :=
  ⟨⟨⟨p.counitSection.app E, by
        ext e; exact p.counit_app_counitSection_app E e⟩⟩⟩

/-! ### Stacks 05UY -/

/-- **Stacks 05UY.** The pushforward `p_*` of a point of a topos commutes with arbitrary
limits, because it is a right adjoint. -/
@[stacks 05UY "commutes with arbitrary limits"]
theorem preservesLimitsOfSize_pushforward : PreservesLimitsOfSize.{w₁, w₂} p.pushforward :=
  p.adj.rightAdjoint_preservesLimits

/-- **Stacks 05UY.** The pushforward `p_*` of a point of a topos is left exact. -/
@[stacks 05UY "is left exact", sga "4 IV 3.1.2" "point; finite limits"]
theorem preservesFiniteLimits_pushforward : PreservesFiniteLimits p.pushforward :=
  have := p.preservesLimitsOfSize_pushforward.{0, 0}
  inferInstance

/-- **Stacks 05UY.** The pushforward `p_*` of a point of a topos is faithful: the counit
`ε_E : p^{-1}p_*E → E` is a (split) epimorphism, and `ε` is natural. -/
@[stacks 05UY "is faithful"]
theorem faithful_pushforward : p.pushforward.Faithful where
  map_injective {E E'} {f g} hfg := by
    have hf := p.adj.counit.naturality f
    have hg := p.adj.counit.naturality g
    simp only [Functor.comp_map, Functor.id_map, hfg] at hf hg
    exact (cancel_epi (p.adj.counit.app E)).1 (hf.symm.trans hg)

/-- **Stacks 05UY.** The pushforward `p_*` of a point of a topos transforms surjections into
surjections: every epimorphism of sets is a *split* epimorphism, and a split epimorphism is
carried to a split epimorphism by any functor. -/
@[stacks 05UY "transforms surjections into surjections. The other claim of the same sentence of
  the source — that `p_*` commutes with coequalizers — is FALSE and is not claimed anywhere in
  this file; see `Point.subsingleton_fiber_of_preservesCoequalizers`"]
theorem preservesEpimorphisms_pushforward : p.pushforward.PreservesEpimorphisms where
  preserves f _ :=
    have := isSplitEpi_of_epi f
    inferInstance

/-- **Stacks 05UY.** The pushforward `p_*` of a point of a topos reflects injections. -/
@[stacks 05UY "reflects injections"]
theorem reflectsMonomorphisms_pushforward : p.pushforward.ReflectsMonomorphisms :=
  have := p.faithful_pushforward
  Functor.reflectsMonomorphisms_of_faithful _

/-- **Stacks 05UY.** The pushforward `p_*` of a point of a topos reflects surjections. -/
@[stacks 05UY "reflects surjections"]
theorem reflectsEpimorphisms_pushforward : p.pushforward.ReflectsEpimorphisms where
  reflects f hf :=
    have := p.faithful_pushforward
    ⟨fun {Z} a b hab =>
      p.pushforward.map_injective
        ((cancel_epi (p.pushforward.map f)).1
          (by rw [← p.pushforward.map_comp, ← p.pushforward.map_comp, hab]))⟩

/-- **Stacks 05UY.** The pushforward `p_*` of a point of a topos reflects isomorphisms: it
reflects both injections and surjections, and a map of sets which is both injective and
surjective is bijective. -/
@[stacks 05UY "reflects isomorphisms"]
theorem reflectsIsomorphisms_pushforward : p.pushforward.ReflectsIsomorphisms where
  reflects f _ := by
    have := p.reflectsMonomorphisms_pushforward
    have := p.reflectsEpimorphisms_pushforward
    have hm : Mono f := p.pushforward.mono_of_mono_map inferInstance
    have he : Epi f := p.pushforward.epi_of_epi_map inferInstance
    rw [isIso_iff_bijective]
    exact ⟨(mono_iff_injective f).1 hm, (epi_iff_surjective f).1 he⟩

end PointOfTopos

/-! ### Stacks 00YA (1) -/

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{w} C]

/-- **Stacks 00YA (1).** Let `p` be a point of the site `C`, given by a fibre functor
`u = Φ.fiber`. Then the pair of functors `(p_*, p^{-1}) = (Φ.skyscraperSheafFunctor,
Φ.sheafFiber)` is a morphism of topoi `Sh(pt) → Sh(C)`, i.e. a point of the topos `Sh(C)` in
the sense of Stacks 00Y4.

The two functors are adjoint by `Point.skyscraperSheafAdjunction`, and `p^{-1}` is left exact
by `Point.sheafFiber_leftExact` (Stacks 00Y5 (3)), which are exactly the two conditions in the
definition of a morphism of topoi (Stacks 00XA). -/
@[stacks 00YA "(1): a point of the site defines a morphism of topoi `Sh(pt) → Sh(C)`",
  sga "4 IV 6.8.7" "(ii)",
  sga "4 IV 7.1" "more general"]
noncomputable def pointOfTopos (Φ : Point.{w} J) : PointOfTopos.{w, v, u} J where
  pushforward := Φ.skyscraperSheafFunctor
  inverseImage := Φ.sheafFiber
  adj := Φ.skyscraperSheafAdjunction
  preservesFiniteLimits := Φ.sheafFiber_leftExact

/-- The pushforward of the point of the topos `Sh(C)` attached to a point `Φ` of the site is
the skyscraper sheaf functor of `Φ`. -/
@[simp]
theorem pointOfTopos_pushforward (Φ : Point.{w} J) :
    (Φ.pointOfTopos).pushforward = Φ.skyscraperSheafFunctor (A := Type w) :=
  rfl

/-- The inverse image of the point of the topos `Sh(C)` attached to a point `Φ` of the site is
the stalk functor of `Φ`. -/
@[simp]
theorem pointOfTopos_inverseImage (Φ : Point.{w} J) :
    (Φ.pointOfTopos).inverseImage = Φ.sheafFiber (A := Type w) :=
  rfl

end CategoryTheory.GrothendieckTopology.Point


namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{max u v} J) (F : Sheaf J (Type max u v) ⥤ Type max u v)
  (α : Φ.fiber ⟶ Sheaf.sheafifiedYoneda J ⋙ F)

/-- The canonical comparison from the presheaf stalk functor, restricted along
`sheafToPresheaf`, to `F`, induced by a natural transformation on the sheafified
representables. On a germ `(U, x, σ)` it is `F(σ)(α_U(x))`, viewing the section `σ` as a map
out of `h_U^#`.

This is `Point.sheafFiberComparison` read through the identification
`Φ.sheafFiber = sheafToPresheaf J _ ⋙ Φ.presheafFiber`
(`Point.sheafToPresheafCompPresheafFiberIso`). Stating it on the composite rather than on
`Φ.sheafFiber` keeps every object in sight of the form `Φ.presheafFiber.obj G.obj`, which is
what makes the colimit lemmas `toPresheafFiber_presheafFiberDesc` apply on the nose. -/
noncomputable def presheafFiberComparison :
    sheafToPresheaf J (Type max u v) ⋙ Φ.presheafFiber ⟶ F where
  app G := Φ.presheafFiberDesc (P := G.obj)
    (fun U x => ↾fun s => F.map ((Sheaf.sectionEquiv J).symm s) (α.app U x))
    (by
      intro U V f x
      ext s
      change F.map ((Sheaf.sectionEquiv J).symm (G.obj.map f.op s)) (α.app U x) =
        F.map ((Sheaf.sectionEquiv J).symm s) (α.app V (Φ.fiber.map f x))
      rw [Sheaf.sectionEquiv_symm_map (F := G), F.map_comp]
      exact congrArg (F.map ((Sheaf.sectionEquiv J).symm s))
        (ConcreteCategory.congr_hom (α.naturality f) x).symm)
  naturality G H f := by
    apply Φ.presheafFiber_hom_ext (P := G.obj)
    intro U x
    change Φ.toPresheafFiber U x G.obj ≫ (Φ.presheafFiber.map f.hom ≫ _) = _
    rw [← Category.assoc, Φ.toPresheafFiber_naturality, Category.assoc,
      Φ.toPresheafFiber_presheafFiberDesc _ _,
      Φ.toPresheafFiber_presheafFiberDesc_assoc _ _]
    ext s
    change F.map ((Sheaf.sectionEquiv J).symm (f.hom.app (Opposite.op U) s))
        (α.app U x) =
      F.map f (F.map ((Sheaf.sectionEquiv J).symm s) (α.app U x))
    rw [Sheaf.sectionEquiv_symm_comp, F.map_comp]
    rfl

/-- The canonical comparison sends the germ of `s` at `(U, x)` to `F(s)(α_U(x))`. -/
@[simp]
theorem presheafFiberComparison_toPresheafFiber (G : Sheaf J (Type max u v))
    (U : C) (x : Φ.fiber.obj U) (s : G.obj.obj (Opposite.op U)) :
    (Φ.presheafFiberComparison F α).app G (Φ.toPresheafFiber U x G.obj s) =
      F.map ((Sheaf.sectionEquiv J).symm s) (α.app U x) :=
  ConcreteCategory.congr_hom
    (Φ.toPresheafFiber_presheafFiberDesc (P := G.obj) _ _ U x) s

/-- The canonical comparison from the stalk functor to `F`, induced by a natural
transformation on the sheafified representables. On a germ `(U, x, σ)` it is
`F(σ)(α_U(x))`, viewing the section `σ` as a map out of `h_U^#`. -/
@[stacks 00YA "(2): the canonical comparison from the reconstructed stalk functor"]
noncomputable def sheafFiberComparison : Φ.sheafFiber ⟶ F where
  app G := (Φ.presheafFiberComparison F α).app G
  naturality _ _ f := (Φ.presheafFiberComparison F α).naturality f

/-- The canonical comparison sends the germ of `s` at `(U, x)` to `F(s)(α_U(x))`. -/
@[simp]
theorem sheafFiberComparison_toPresheafFiber (G : Sheaf J (Type max u v))
    (U : C) (x : Φ.fiber.obj U) (s : G.obj.obj (Opposite.op U)) :
    (Φ.sheafFiberComparison F α).app G (Φ.toPresheafFiber U x G.obj s) =
      F.map ((Sheaf.sectionEquiv J).symm s) (α.app U x) :=
  Φ.presheafFiberComparison_toPresheafFiber F α G U x s

end CategoryTheory.GrothendieckTopology.Point

namespace PointOfTopos

private theorem precomp_elements_full {C : Type u} [Category.{v} C]
    {D : Type w₁} [Category.{w₂} D] (F : C ⥤ D) (G : D ⥤ Type w)
    [F.Full] : (Functor.Elements.precomp F G).Full := by
  constructor
  intro x y f
  obtain ⟨g, hg⟩ := F.map_surjective f.hom
  refine ⟨Functor.Elements.homMk g ?_, ?_⟩
  · show G.map (F.map g) x.val = y.val
    rw [hg]
    exact f.map_val
  · exact Functor.Elements.hom_ext hg

private theorem precomp_elements_faithful {C : Type u} [Category.{v} C]
    {D : Type w₁} [Category.{w₂} D] (F : C ⥤ D) (G : D ⥤ Type w)
    [F.Faithful] : (Functor.Elements.precomp F G).Faithful := by
  constructor
  intro x y f g h
  exact Functor.Elements.hom_ext (F.map_injective (congrArg Functor.Elements.Hom.hom h))

private theorem cofiltered_elements_comp_of_full_faithful
    {C : Type u} [Category.{v} C] {D : Type w₁} [Category.{w₂} D]
    (F : C ⥤ D) (G : D ⥤ Type w) [F.Full] [F.Faithful]
    [IsCofiltered G.Elements]
    (h : ∀ d : G.Elements, ∃ c : (F ⋙ G).Elements,
      Nonempty ((Functor.Elements.precomp F G).obj c ⟶ d)) :
    IsCofiltered (F ⋙ G).Elements := by
  have := precomp_elements_full F G
  have := precomp_elements_faithful F G
  exact IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful
    (Functor.Elements.precomp F G) h

private theorem isCofiltered_presheafFiber
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (p : PointOfTopos.{max u v, v, u} J) :
    IsCofiltered
      ((presheafToSheaf J (Type max u v) ⋙ p.inverseImage).Elements) := by
  have := p.preservesFiniteLimits
  have : PreservesFiniteLimits
      (presheafToSheaf J (Type max u v) ⋙ p.inverseImage) := inferInstance
  have : HasFiniteLimits
      ((presheafToSheaf J (Type max u v) ⋙ p.inverseImage).Elements) :=
    ⟨fun I _ _ => inferInstance⟩
  exact IsCofiltered.of_hasFiniteLimits _

/-- Every element of `p⁻¹(P^#)` comes from `p⁻¹(h_U^#)` along a map of the canonical
colimit presentation of `P` by representables. -/
private theorem exists_map_coconeOfRepresentable_eq
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (p : PointOfTopos.{max u v, v, u} J) (P : Cᵒᵖ ⥤ Type max u v)
    (x : (presheafToSheaf J (Type max u v) ⋙ p.inverseImage).obj P) :
    ∃ (j : P.Elementsᵒᵖ)
      (z : (presheafToSheaf J (Type max u v) ⋙ p.inverseImage).obj
        ((Presheaf.functorToRepresentables P).obj j)),
      (presheafToSheaf J (Type max u v) ⋙ p.inverseImage).map
        ((Presheaf.coconeOfRepresentable P).ι.app j) z = x := by
  have : PreservesColimitsOfSize.{v, max u v} (presheafToSheaf J (Type max u v)) :=
    (sheafificationAdjunction J (Type max u v)).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{v, max u v} p.inverseImage :=
    p.adj.leftAdjoint_preservesColimits
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (presheafToSheaf J (Type max u v) ⋙ p.inverseImage)
      (Presheaf.colimitOfRepresentable P)) x

private theorem isCofiltered_sheafifiedYoneda_fiber
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (p : PointOfTopos.{max u v, v, u} J) :
    IsCofiltered (Sheaf.sheafifiedYoneda J ⋙ p.inverseImage).Elements := by
  let F : C ⥤ Cᵒᵖ ⥤ Type max u v := uliftYoneda.{u}
  let G : (Cᵒᵖ ⥤ Type max u v) ⥤ Type max u v :=
    presheafToSheaf J (Type max u v) ⋙ p.inverseImage
  have : IsCofiltered G.Elements := p.isCofiltered_presheafFiber
  have : F.Full := inferInstance
  have : F.Faithful := inferInstance
  show IsCofiltered (F ⋙ G).Elements
  apply cofiltered_elements_comp_of_full_faithful F G
  rintro @⟨P, x⟩
  obtain ⟨j, y, hy⟩ := p.exists_map_coconeOfRepresentable_eq P x
  exact ⟨.mk (obj := j.unop.obj.unop) y,
    ⟨Functor.Elements.homMk ((Presheaf.coconeOfRepresentable P).ι.app j) hy⟩⟩

private theorem initiallySmall_sheafifiedYoneda_fiber
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (p : PointOfTopos.{max u v, v, u} J) :
    InitiallySmall.{max u v} (Sheaf.sheafifiedYoneda J ⋙ p.inverseImage).Elements := by
  have : EssentiallySmall.{max u v} C := inferInstance
  have : EssentiallySmall.{max u v}
      (Sheaf.sheafifiedYoneda J ⋙ p.inverseImage).Elements := inferInstance
  exact initiallySmall_of_essentiallySmall _

private theorem sieve_uliftFunctorInclusion_isIso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {X : C} (S : Sieve X) (hS : S ∈ J X) :
    IsIso ((presheafToSheaf J (Type max u v)).map
      (Sieve.uliftFunctorInclusion.{u} S)) := by
  let f := Sieve.uliftFunctorInclusion.{u} S
  have : Presheaf.IsLocallyInjective J f :=
    Presheaf.isLocallyInjective_of_injective J f (fun Y x y h => by
      apply ULift.ext
      apply Subtype.ext
      change ULift.up x.down.1 = ULift.up y.down.1 at h
      exact congrArg ULift.down h)
  have : Presheaf.IsLocallySurjective J f := by
    constructor
    intro U s
    have h : Presheaf.imageSieve f s = S.pullback s.down := by
      ext V g
      constructor
      · rintro ⟨t, ht⟩
        rcases t with ⟨⟨k, hk⟩⟩
        change ULift.up k = ULift.up (g ≫ s.down) at ht
        show S (g ≫ s.down)
        have h' : k = g ≫ s.down := by simpa using congrArg ULift.down ht
        exact h' ▸ hk
      · exact fun hg => ⟨ULift.up ⟨g ≫ s.down, hg⟩, rfl⟩
    rw [h]
    exact J.pullback_stable s.down hS
  rw [← J.W_iff]
  exact J.W_of_isLocallyBijective f

private theorem sieve_coconeOfRepresentable_comp
    {C : Type u} [Category.{v} C] {X : C} (S : Sieve X)
    (j : (S.uliftFunctor.{u}).Elementsᵒᵖ) :
    (Presheaf.coconeOfRepresentable (S.uliftFunctor.{u})).ι.app j ≫
      S.uliftFunctorInclusion =
        uliftYoneda.map j.unop.val.down.1 := by
  ext Y t
  rfl

/-- **Stacks 00YA (2).** Every point `p` of the topos arises from a point of the site
whose fiber functor is `U ↦ p⁻¹(h_U^#)` on the nose.

`PointOfTopos.exists_sitePoint` is the same reconstruction stated up to isomorphism of stalk
functors; this form is the one consumers need when they have to transport along the identity of
fibre functors with `eqToIso`. -/
@[stacks 00YA "(2): reconstruction of the site point"]
theorem exists_sitePoint_fiber_eq {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (p : PointOfTopos.{max u v, v, u} J) :
    ∃ Φ : GrothendieckTopology.Point.{max u v} J,
      Φ.fiber = Sheaf.sheafifiedYoneda J ⋙ p.inverseImage := by
  let F := Sheaf.sheafifiedYoneda J ⋙ p.inverseImage
  have : IsCofiltered F.Elements := p.isCofiltered_sheafifiedYoneda_fiber
  have : InitiallySmall.{max u v} F.Elements :=
    p.initiallySmall_sheafifiedYoneda_fiber
  refine ⟨{ fiber := F, jointly_surjective := ?_ }, rfl⟩
  intro X S hS x
  let P := S.uliftFunctor.{u}
  let G := presheafToSheaf J (Type max u v) ⋙ p.inverseImage
  let f := S.uliftFunctorInclusion.{u}
  have : IsIso ((presheafToSheaf J (Type max u v)).map f) :=
    sieve_uliftFunctorInclusion_isIso J S hS
  have : IsIso (G.map f) := by
    dsimp [G]
    infer_instance
  let y : G.obj P := inv (G.map f) x
  obtain ⟨j, z, hz⟩ := p.exists_map_coconeOfRepresentable_eq P y
  refine ⟨j.unop.obj.unop, j.unop.val.down.1, j.unop.val.down.2, z, ?_⟩
  show G.map (uliftYoneda.map j.unop.val.down.1) z = x
  let l := (Presheaf.coconeOfRepresentable P).ι.app j
  have hz' : G.map l z = y := hz
  have hmaps : G.map (uliftYoneda.map j.unop.val.down.1) =
      G.map l ≫ G.map f :=
    (congrArg G.map (sieve_coconeOfRepresentable_comp S j)).symm.trans (G.map_comp l f)
  have hcalc : G.map (uliftYoneda.map j.unop.val.down.1) z =
      G.map f (G.map l z) :=
    (ConcreteCategory.congr_hom hmaps z).trans
      (CategoryTheory.comp_apply (G.map l) (G.map f) z)
  rw [hcalc, hz']
  exact IsIso.inv_hom_id_apply (G.map f) x

private noncomputable def fiberToSheafYoneda
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (Φ : GrothendieckTopology.Point.{max u v} J) (X : C) :
    Φ.fiber.obj X ≅ Φ.sheafFiber.obj ((Sheaf.sheafifiedYoneda J).obj X) :=
  ((Φ.shrinkYonedaCompPresheafFiberIso.app X).symm ≪≫
    Φ.presheafFiber.mapIso (uliftYonedaIsoShrinkYoneda.{u}.app X).symm) ≪≫
      ((Φ.presheafToSheafCompSheafFiberIso (Type max u v)).app
        (uliftYoneda.obj X)).symm

private theorem fiberToSheafYoneda_hom_apply
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (Φ : GrothendieckTopology.Point.{max u v} J) (X : C) (x : Φ.fiber.obj X) :
    (fiberToSheafYoneda Φ X).hom x =
      Φ.toPresheafFiber X x ((Sheaf.sheafifiedYoneda J).obj X).obj
        (Sheaf.sectionEquiv J (𝟙 ((Sheaf.sheafifiedYoneda J).obj X))) := by
  let P := uliftYoneda.{u}.obj X
  let Q := shrinkYoneda.{max u v}.obj X
  let ψ : Q ⟶ P := (uliftYonedaIsoShrinkYoneda.{u}.app X).inv
  let η : P ⟶ ((Sheaf.sheafifiedYoneda J).obj X).obj := toSheafify J P
  show Φ.presheafFiber.map η
      (Φ.presheafFiber.map ψ
        (Φ.shrinkYonedaCompPresheafFiberIso.inv.app X x)) =
      Φ.toPresheafFiber X x ((Sheaf.sheafifiedYoneda J).obj X).obj
        (Sheaf.sectionEquiv J (𝟙 ((Sheaf.sheafifiedYoneda J).obj X)))
  rw [Φ.shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber,
    Φ.toPresheafFiber_naturality_apply ψ X x, Φ.toPresheafFiber_naturality_apply η X x]
  have hψ : ψ.app (Opposite.op X)
      (shrinkYonedaObjObjEquiv.symm (𝟙 X)) = ULift.up (𝟙 X) := by
    simp only [Iso.app_inv, uliftYonedaIsoShrinkYoneda, NatIso.ofComponents_inv_app,
      Equiv.toIso_inv_hom_apply, Equiv.symm_trans, Equiv.symm_symm, Equiv.trans_apply,
      Equiv.apply_symm_apply, ψ]
    exact ULift.ext (Equiv.ulift_symm_down.{u, v} (𝟙 X))
  rw [hψ]
  have harg : (toSheafify J P).app (Opposite.op X) (Equiv.ulift.symm (𝟙 X)) =
      Sheaf.sectionEquiv J (𝟙 ((Sheaf.sheafifiedYoneda J).obj X)) := by
    simpa [P] using (Sheaf.sectionEquiv_id J X).symm
  exact congrArg (Φ.toPresheafFiber X x ((Sheaf.sheafifiedYoneda J).obj X).obj) harg

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (p : PointOfTopos.{max u v, v, u} J) (Φ : GrothendieckTopology.Point.{max u v} J)
  (e : Φ.fiber ≅ Sheaf.sheafifiedYoneda J ⋙ p.inverseImage)

/-- **Stacks 00YA (2).** The canonical comparison identifies the reconstructed stalk
functor with `p.inverseImage`. -/
@[stacks 00YA "(2): the canonical inverse-image comparison is an isomorphism"]
theorem isIso_sheafFiberComparison :
    IsIso (Φ.sheafFiberComparison p.inverseImage e.hom) := by
  let α := Φ.sheafFiberComparison p.inverseImage e.hom
  have hgen (X : C) : IsIso (α.app ((Sheaf.sheafifiedYoneda J).obj X)) := by
    have h : (fiberToSheafYoneda Φ X).hom ≫
        α.app ((Sheaf.sheafifiedYoneda J).obj X) = e.hom.app X := by
      ext x
      show α.app _ ((fiberToSheafYoneda Φ X).hom x) = e.hom.app X x
      rw [fiberToSheafYoneda_hom_apply,
        GrothendieckTopology.Point.sheafFiberComparison_toPresheafFiber, Equiv.symm_apply_apply,
        p.inverseImage.map_id]
      exact CategoryTheory.id_apply
        (X := p.inverseImage.obj ((Sheaf.sheafifiedYoneda J).obj X))
        (e.hom.app X x)
    exact IsIso.of_isIso_fac_left h
  have (H : Sheaf J (Type max u v)) : IsIso (α.app H) := by
    let K := Sheaf.indexingDiagram J H ⋙ Sheaf.sheafifiedYoneda J
    have : ∀ i, IsIso ((Functor.whiskerLeft K α).app i) := fun i => hgen _
    have : IsIso (Functor.whiskerLeft K α) :=
      NatIso.isIso_of_isIso_app _
    have : PreservesColimit K Φ.sheafFiber :=
      Φ.skyscraperSheafAdjunction.leftAdjoint_preservesColimits
        |>.preservesColimitsOfShape.preservesColimit
    have : PreservesColimit K p.inverseImage :=
      (p.adj.leftAdjoint_preservesColimits).preservesColimitsOfShape.preservesColimit
    exact isIso_app_coconePt_of_preservesColimit K α
      (Sheaf.coconeOfRepresentable J H) (Sheaf.colimitOfRepresentable J H)
  exact NatIso.isIso_of_isIso_app α

/-- **Stacks 00YA (2).** The adjoint mate of the canonical comparison is an isomorphism
`p.pushforward ⟶ Φ.skyscraperSheafFunctor`, recovering the pushforward compatibly with
the given adjunctions. -/
@[stacks 00YA "(2): recovery of the pushforward by the adjoint mate"]
theorem isIso_conjugate_sheafFiberComparison :
    IsIso (conjugateEquiv p.adj Φ.skyscraperSheafAdjunction
      (Φ.sheafFiberComparison p.inverseImage e.hom)) := by
  have := p.isIso_sheafFiberComparison Φ e
  infer_instance

end PointOfTopos

/-! ### `p_*E(U) = Map(u(U), E)`, and the failure of the coequalizer clause of Stacks 05UY -/

namespace CategoryTheory.GrothendieckTopology.Point

open Limits Opposite
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- In `Type w`, a product of copies of `E` indexed by a set `A` is the set of functions
`A → E`. This is the identification under which Mathlib's skyscraper presheaf, defined as a
product, becomes the presheaf `U ↦ Map(u(U), E)` of Stacks 04EI. -/
noncomputable def piConstIso (A E : Type w) : (∏ᶜ fun (_ : A) => E) ≅ (A ⟶ E) :=
  Limits.Types.productIso.{w, w} (fun (_ : A) => E) ≪≫ TypeCat.homEquiv.symm.toIso

/-- `piConstIso` turns a section of `∏_{a ∈ A} E` into the function reading off its
components: its value at `a` is the `a`-th projection of the section. -/
@[simp]
theorem piConstIso_hom_apply (A E : Type w) (s : ∏ᶜ fun (_ : A) => E) (a : A) :
    (piConstIso A E).hom s a = Pi.π (fun (_ : A) => E) a s := by simp [piConstIso]

/-- Reindexing a product of copies of `E` along `p : B → A` is precomposition with `p` on
components: the `b`-th component of the reindexed section is the `p b`-th component. -/
@[simp]
theorem pi_map'_const_π_apply {A B E : Type w} (p : B → A) (s : ∏ᶜ fun (_ : A) => E) (b : B) :
    Pi.π (fun (_ : B) => E) b
        (Pi.map' (f := fun (_ : A) => E) (g := fun (_ : B) => E) p (fun _ => 𝟙 E) s) =
      Pi.π (fun (_ : A) => E) (p b) s := by
  simpa only [CategoryTheory.comp_apply, Category.comp_id] using
    ConcreteCategory.congr_hom
      (Pi.map'_comp_π (C := Type w) (f := fun (_ : A) => E) (g := fun (_ : B) => E) p
        (fun _ => 𝟙 E) b)
      s

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The formula of Stacks 04EI for Mathlib's skyscraper presheaf.** For a point `Φ` of a
site with fibre functor `u = Φ.fiber`, the skyscraper presheaf `u^pE` is the presheaf
`U ↦ Map(u(U), E)`, with restriction maps given by precomposition with `u`.

Mathlib defines it as the product `∏_{x ∈ u(U)} E`; this is the identification of that
product with the set of functions `u(U) → E`. -/
noncomputable def skyscraperPresheafIsoYoneda (Φ : Point.{w} J) (E : Type w) :
    Φ.skyscraperPresheaf E ≅ Φ.fiber.op ⋙ CategoryTheory.yoneda.obj E :=
  NatIso.ofComponents (fun _ => piConstIso _ E)
    (fun {X Y} f => by
      ext s
      apply TypeCat.homEquiv.injective
      funext y
      simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The same identification, read as a natural isomorphism in `E` after evaluating at a fixed
object `X`: the functor `E ↦ u^pE(X)` is the functor `E ↦ Map(u(X), E)`. -/
noncomputable def skyscraperEvalIsoCoyoneda (Φ : Point.{w} J) (X : C) :
    Φ.skyscraperPresheafFunctor (A := Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj (op X) ≅
      CategoryTheory.coyoneda.obj (op (Φ.fiber.obj X)) :=
  NatIso.ofComponents (fun E => piConstIso _ E)
    (fun {E E'} g => by
      ext s
      apply TypeCat.homEquiv.injective
      funext y
      simp [Types.pi_map_π_apply'])

/-- If a set `A` has two distinct elements then `Map(A, -) : Type w ⥤ Type w` does **not**
preserve coequalizers.

Take `f₀, f₁ : pt ⇉ B` with `B` a two-element set, picking out the two elements. Their
coequalizer `Q` is a singleton, so `Map(A, Q)` is a singleton too, and therefore every map out
of `Map(A, B)` that equalizes `Map(A, f₀)` and `Map(A, f₁)` would have to be constant. The map
`g ↦ (g a = g b)` equalizes them — both `Map(A, f₀)` and `Map(A, f₁)` land in the constant
functions — and is not constant. -/
theorem not_preservesCoequalizers_coyoneda {A : Type w} {a b : A} (hab : a ≠ b) :
    ¬PreservesColimitsOfShape WalkingParallelPair
        (CategoryTheory.coyoneda.obj (op A) : Type w ⥤ Type w) := by
  classical
  intro hpres
  let B : Type w := ULift.{w} Bool
  have hne : (ULift.up true : B) ≠ ULift.up false := fun h => by simpa using congrArg ULift.down h
  let f₀ : (PUnit.{w + 1} : Type w) ⟶ B := ↾fun _ => ULift.up true
  let f₁ : (PUnit.{w + 1} : Type w) ⟶ B := ↾fun _ => ULift.up false
  -- the coequalizer of `f₀` and `f₁` in `Type w` is a subsingleton
  have hcond : (coequalizer.π f₀ f₁) (ULift.up true) = (coequalizer.π f₀ f₁) (ULift.up false) := by
    simpa [f₀, f₁] using ConcreteCategory.congr_hom (coequalizer.condition f₀ f₁) PUnit.unit
  have hsurj := (epi_iff_surjective (coequalizer.π f₀ f₁)).1 inferInstance
  have hQ : Subsingleton (coequalizer f₀ f₁) := by
    refine ⟨fun q q' => ?_⟩
    obtain ⟨⟨x⟩, rfl⟩ := hsurj q
    obtain ⟨⟨y⟩, rfl⟩ := hsurj q'
    cases x <;> cases y <;>
      first
      | rfl
      | exact hcond
      | exact hcond.symm
  have hQ' : Subsingleton ((CategoryTheory.coyoneda.obj (op A)).obj (coequalizer f₀ f₁)) :=
    ⟨fun x y => TypeCat.homEquiv.injective (funext fun _ => hQ.elim _ _)⟩
  -- a map out of `Map(A, B)` equalizing `Map(A, f₀)` and `Map(A, f₁)` which is not constant
  let g₀ : A ⟶ B := ↾fun _ => ULift.up true
  let g₁ : A ⟶ B := ↾fun x => if x = a then ULift.up true else ULift.up false
  let φ : (CategoryTheory.coyoneda.obj (op A)).obj B ⟶ B :=
    ↾fun (g : A ⟶ B) => if g a = g b then ULift.up true else ULift.up false
  have hφ :
    (CategoryTheory.coyoneda.obj (op A)).map f₀ ≫ φ =
      (CategoryTheory.coyoneda.obj (op A)).map f₁ ≫ φ := by
    ext s
    simp [φ, f₀, f₁]
  have hfac := Cofork.IsColimit.π_desc (t := Cofork.ofπ φ hφ)
    (isColimitOfHasCoequalizerOfPreservesColimit (CategoryTheory.coyoneda.obj (op A)) f₀ f₁)
  have key : φ g₀ = φ g₁ := by
    have h0 := ConcreteCategory.congr_hom hfac g₀
    have h1 := ConcreteCategory.congr_hom hfac g₁
    simp only [Cofork.π_ofπ, CategoryTheory.comp_apply] at h0 h1
    rw [← h0, ← h1,
      hQ'.elim ((CategoryTheory.coyoneda.obj (op A)).map (coequalizer.π f₀ f₁) g₀)
        ((CategoryTheory.coyoneda.obj (op A)).map (coequalizer.π f₀ f₁) g₁)]
  simp [φ, g₀, g₁, Ne.symm hab, hne] at key

/-- **The coequalizer clause of Stacks 05UY fails.** For a point `Φ` of a site `(C, J)`, if the
skyscraper presheaf functor `E ↦ u^pE` commutes with coequalizers, then every `u(X)` is a
subsingleton — so the clause forces a degenerate point.

Combined with the identification `u^pE(X) = Map(u(X), E)`
(`skyscraperPresheafIsoYoneda`, Stacks 04EI), this is exactly the failure of the step "it
follows immediately from this formula" in the Stacks proof of 05UY: `Map(A, -)` preserves
surjections but not coequalizers.

For the topology `J = ⊥` the sheaves are the presheaves and coequalizers of sheaves are
computed objectwise, so this yields an actual counterexample to the clause as stated for
`p_* : Set ⥤ Sh(C)`: take `C = WalkingParallelPair`, `J = ⊥` and `Φ = pointBot zero`
(Mathlib's `GrothendieckTopology.pointBot`), whose fibre functor is `Hom(zero, -)`, so that
`u(one) = {left, right}` has two elements. The transport of the statement below across
`Sh(C, ⊥) ≃ PSh(C)` is not formalized here. -/
theorem subsingleton_fiber_of_preservesCoequalizers (Φ : Point.{w} J)
    (h : PreservesColimitsOfShape WalkingParallelPair (Φ.skyscraperPresheafFunctor (A := Type w)))
    (X : C) : Subsingleton (Φ.fiber.obj X) := by
  by_contra hns
  rw [not_subsingleton_iff_nontrivial] at hns
  obtain ⟨a, b, hab⟩ := hns.exists_pair_ne
  refine not_preservesCoequalizers_coyoneda hab ?_
  have hcomp :
    PreservesColimitsOfShape WalkingParallelPair
      (Φ.skyscraperPresheafFunctor (A := Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj (op X)) :=
    inferInstance
  exact preservesColimitsOfShape_of_natIso (Φ.skyscraperEvalIsoCoyoneda X)

end CategoryTheory.GrothendieckTopology.Point
