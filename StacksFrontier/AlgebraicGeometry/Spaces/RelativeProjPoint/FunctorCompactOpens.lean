module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.AlgebraicSpace

/-!
# The functor `F` of Stacks 084A: its values, restriction maps and morphism to `X`

In Situation 0849 the functor `F` of Stacks 084A is
`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjFunctor`, with its morphism
`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjπ` to `X`.  The source defines it in
four steps:

1. for a quasi-compact test scheme `T`, `F(T)` is the set of equivalence classes of quadruples
   `(d, f, ℒ, ψ)` over `T` — this is
   `AlgebraicGeometry.Space.RelativeProjSituation.relativeProjFunctorEquivF`;
2. a morphism `h : T' ⟶ T` pulls a quadruple back to `(d, f ∘ h, h^*ℒ, h^*ψ)`, and pullback
   preserves the equivalence relation;
3. for an arbitrary test scheme `T`, `F(T) = lim_{V ⊆ T quasi-compact open} F(V)`;
4. `F ⟶ X` sends the quadruple `(d, f, ℒ, ψ)` to `f`.

This file proves that `relativeProjFunctor` has the properties (2), (3) and (4).

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.relativeProjFunctorEquivF_map_mk`: on
  quasi-compact test objects the restriction map of `F` along `h : T' ⟶ T` sends the class of a
  quadruple `(d, f, ℒ, ψ)` to the class of its pullback `(d, f ∘ h, h^*ℒ, h^*ψ)`.
* `AlgebraicGeometry.Space.RelativeProjSituation.bijective_restrictCompactOpens`: for every test
  object `T` the map from `F(T)` to the compatible families `(ξ_V)` of classes of quadruples over
  the quasi-compact opens `V` of `T`, `x ↦ (x|_V)`, is a bijection: `F(T) = lim_V F(V)`.
* `AlgebraicGeometry.Space.RelativeProjSituation.relativeProjπ_app_mk`: `F ⟶ X` sends the class
  of `(d, f, ℒ, ψ)` to `f`.
* `AlgebraicGeometry.Space.SiteQcExtension.equivCompactOpens`: for any presheaf `Φ` on the big
  fppf site, the limit of `Φ` over the quasi-compact test objects over `T`, which the library
  uses to define `F`, is the limit over the quasi-compact opens of `T`.

## Implementation notes

The library's `F` is indexed by all morphisms `W ⟶ T` out of quasi-compact test objects, which
makes the functoriality in `T` a reindexing; `equivCompactOpens` shows that restricting to the
inclusions of the quasi-compact opens loses nothing.  Its two halves are that every morphism out
of a quasi-compact test object factors through a quasi-compact open
(`AlgebraicGeometry.Scheme.compactOpenFactorization`), and that two factorizations agree after
the inclusion into the union of their two opens, the inclusion of an open being a monomorphism.
This is the site-level counterpart of `AlgebraicGeometry.Scheme.QcExtension.equivQcOpen`.

## References

* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u m

namespace AlgebraicGeometry.Space

/-! ### The limit over the quasi-compact opens of a test object -/

section CompactOpens

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Morphisms into a Zariski open of a test object are determined by their composites with the
inclusion**, the inclusion of an open subscheme being a monomorphism. -/
theorem opensObjectι_hom_ext {T W : BigFppfOver B S hS}
    {V : ((BigFppfOver.toScheme B S hS).obj T).Opens} {a b : W ⟶ opensObject B S hS T V}
    (h : a ≫ opensObjectι B S hS T V = b ≫ opensObjectι B S hS T V) : a = b := by
  apply BigFppfOver.map_toScheme_injective B S hS
  have h' := congrArg (BigFppfOver.toScheme B S hS).map h
  rw [Functor.map_comp, Functor.map_comp, toScheme_map_opensObjectι] at h'
  exact (cancel_mono V.ι).1 h'

/-- The quasi-compact open of the scheme of `T` through which the chosen factorization of a
morphism `w : W ⟶ T` out of a quasi-compact test object passes,
`AlgebraicGeometry.Scheme.compactOpenFactorization`. -/
def factorOpens {T W : BigFppfOver B S hS}
    (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W)) (w : W ⟶ T) :
    ((BigFppfOver.toScheme B S hS).obj T).CompactOpens :=
  ⟨(Scheme.compactOpenFactorization hW ((BigFppfOver.toScheme B S hS).map w)).opens,
    (Scheme.compactOpenFactorization hW ((BigFppfOver.toScheme B S hS).map w)).isCompact_opens⟩

/-- The chosen factorization of a morphism `w : W ⟶ T` out of a quasi-compact test object through
the quasi-compact open `AlgebraicGeometry.Space.factorOpens` of the scheme of `T`. -/
def factorThrough {T W : BigFppfOver B S hS}
    (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W)) (w : W ⟶ T) :
    W ⟶ opensObject B S hS T (factorOpens hW w).1 :=
  GradedAlgebraRestriction.factorHom w
    (Scheme.compactOpenFactorization hW ((BigFppfOver.toScheme B S hS).map w))

/-- The chosen factorization `AlgebraicGeometry.Space.factorThrough` of `w`, followed by the
inclusion of the quasi-compact open, is `w`. -/
theorem factorThrough_ι {T W : BigFppfOver B S hS}
    (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W)) (w : W ⟶ T) :
    factorThrough hW w ≫ opensObjectι B S hS T (factorOpens hW w).1 = w :=
  GradedAlgebraRestriction.factorHom_ι w _

namespace SiteQcExtension

variable {Φ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}

/-- **The limit `lim_{V ⊆ T quasi-compact open} Φ(V)` of Stacks 084A**: the families of elements
of `Φ(V)`, one for each quasi-compact open `V` of the scheme of `T`, compatible with the
inclusions between them. -/
abbrev CompactOpensLimit (Φ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v) (T : BigFppfOver B S hS) :
    Type (max u v) :=
  {ξ : ∀ V : ((BigFppfOver.toScheme B S hS).obj T).CompactOpens,
      Φ.obj (op (opensObject B S hS T V.1)) //
    ∀ (V V' : ((BigFppfOver.toScheme B S hS).obj T).CompactOpens) (h : V'.1 ≤ V.1),
      Φ.map (GradedAlgebraRestriction.opensObjectHomOfLE T h).op (ξ V) = ξ V'}

/-- Restricting a family indexed by the quasi-compact test objects over `T` to the inclusions of
the quasi-compact opens of `T`. -/
def restrictCompactOpens {T : BigFppfOver B S hS} (s : SiteQcExtension Φ T) :
    CompactOpensLimit Φ T :=
  ⟨fun V => s.val _ (compactSpace_opensObject T V) (opensObjectι B S hS T V.1),
    fun V V' h => (s.compat _ _ (compactSpace_opensObject T V) (compactSpace_opensObject T V')
      (GradedAlgebraRestriction.opensObjectHomOfLE T h) (opensObjectι B S hS T V.1)).trans
      (congrArg (s.val _ (compactSpace_opensObject T V'))
        (GradedAlgebraRestriction.opensObjectHomOfLE_ι T h))⟩

/-- **The value a compatible family over the quasi-compact opens assigns to a morphism does not
depend on the quasi-compact open it is factored through**: two factorizations agree after the
inclusion into the union of their opens. -/
theorem map_eq_map_of_comp_ι_eq {T : BigFppfOver B S hS} (ξ : CompactOpensLimit Φ T)
    {W : BigFppfOver B S hS} (V V' : ((BigFppfOver.toScheme B S hS).obj T).CompactOpens)
    (k : W ⟶ opensObject B S hS T V.1) (k' : W ⟶ opensObject B S hS T V'.1)
    (hk : k ≫ opensObjectι B S hS T V.1 = k' ≫ opensObjectι B S hS T V'.1) :
    Φ.map k.op (ξ.1 V) = Φ.map k'.op (ξ.1 V') := by
  let U : ((BigFppfOver.toScheme B S hS).obj T).CompactOpens :=
    ⟨V.1 ⊔ V'.1, by rw [TopologicalSpace.Opens.coe_sup]; exact V.2.union V'.2⟩
  have hV : V.1 ≤ U.1 := le_sup_left
  have hV' : V'.1 ≤ U.1 := le_sup_right
  have hkk : k ≫ GradedAlgebraRestriction.opensObjectHomOfLE T hV =
      k' ≫ GradedAlgebraRestriction.opensObjectHomOfLE T hV' := by
    apply opensObjectι_hom_ext
    rw [Category.assoc, Category.assoc, GradedAlgebraRestriction.opensObjectHomOfLE_ι,
      GradedAlgebraRestriction.opensObjectHomOfLE_ι, hk]
  rw [← ξ.2 U V hV, ← ξ.2 U V' hV', ← FunctorToTypes.map_comp_apply,
    ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp, hkk]

/-- Extending a compatible family over the quasi-compact opens of `T` to all quasi-compact test
objects over `T`: the value at `w : W ⟶ T` is the value at a quasi-compact open through which
`w` factors, pulled back along the factorization. -/
def extendCompactOpens {T : BigFppfOver B S hS} (ξ : CompactOpensLimit Φ T) :
    SiteQcExtension Φ T where
  val W hW w := Φ.map (factorThrough hW w).op (ξ.1 (factorOpens hW w))
  compat W W' hW hW' h w := by
    refine (FunctorToTypes.map_comp_apply Φ _ _ _).symm.trans ?_
    rw [← op_comp]
    exact map_eq_map_of_comp_ι_eq ξ (factorOpens hW w) (factorOpens hW' (h ≫ w)) _ _
      (by rw [Category.assoc, factorThrough_ι, factorThrough_ι])

/-- Extending the restriction of a family over the quasi-compact test objects over `T` to the
quasi-compact opens of `T` recovers the family. -/
theorem extendCompactOpens_restrictCompactOpens {T : BigFppfOver B S hS}
    (s : SiteQcExtension Φ T) : extendCompactOpens s.restrictCompactOpens = s := by
  ext W hW w
  exact (s.compat _ W (compactSpace_opensObject T (factorOpens hW w)) hW (factorThrough hW w)
    (opensObjectι B S hS T (factorOpens hW w).1)).trans
      (congrArg (s.val W hW) (factorThrough_ι hW w))

/-- Restricting the extension of a compatible family over the quasi-compact opens of `T` to the
inclusions of those opens recovers the family. -/
theorem restrictCompactOpens_extendCompactOpens {T : BigFppfOver B S hS}
    (ξ : CompactOpensLimit Φ T) : (extendCompactOpens ξ).restrictCompactOpens = ξ := by
  apply Subtype.ext
  funext V
  have h1 := map_eq_map_of_comp_ι_eq ξ
    (factorOpens (compactSpace_opensObject T V) (opensObjectι B S hS T V.1)) V
    (factorThrough _ _) (𝟙 _) ((factorThrough_ι _ _).trans (Category.id_comp _).symm)
  rwa [op_id, FunctorToTypes.map_id_apply] at h1

/-- **The limit over the quasi-compact test objects over `T` is the limit over the quasi-compact
opens of `T`**: restricting to the inclusions of the quasi-compact opens is a bijection. -/
def equivCompactOpens (T : BigFppfOver B S hS) :
    SiteQcExtension Φ T ≃ CompactOpensLimit Φ T where
  toFun := restrictCompactOpens
  invFun := extendCompactOpens
  left_inv := extendCompactOpens_restrictCompactOpens
  right_inv := restrictCompactOpens_extendCompactOpens

/-- The component of `equivCompactOpens T s` at a quasi-compact open `V` of `T` is the value of
`s` at the inclusion of `V`. -/
@[simp] theorem equivCompactOpens_apply_coe {T : BigFppfOver B S hS} (s : SiteQcExtension Φ T)
    (V : ((BigFppfOver.toScheme B S hS).obj T).CompactOpens) :
    (equivCompactOpens T s).1 V =
      s.val _ (compactSpace_opensObject T V) (opensObjectι B S hS T V.1) :=
  rfl

end SiteQcExtension

end CompactOpens

/-! ### The functor `F` of Stacks 084A -/

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-- The value at the identity of the class of the restriction of `x` to `T'` is the value of the
class of `x` at `τ : T' ⟶ T`. -/
private theorem quadrupleSpaceEquiv_map_val_id {T T' : BigFppfOver s.site s.base s.containsBase}
    (τ : T' ⟶ T) (hT' : CompactSpace ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T'))
    (x : s.relativeProjFunctor.obj (op T)) :
    (s.quadrupleRestriction.quadrupleSpaceEquiv s.shrink.contains_relativeProj_pointAlgebra
      s.shrink.space.property.isSheaf T' (s.relativeProjFunctor.map τ.op x)).val T' hT' (𝟙 T') =
    (s.quadrupleRestriction.quadrupleSpaceEquiv s.shrink.contains_relativeProj_pointAlgebra
      s.shrink.space.property.isSheaf T x).val T' hT' τ :=
  (congrArg (fun y => SiteQcExtension.val y T' hT' (𝟙 T'))
    (s.quadrupleRestriction.quadrupleSpaceEquiv_map s.shrink.contains_relativeProj_pointAlgebra
      s.shrink.space.property.isSheaf τ x)).trans (congrArg (SiteQcExtension.val _ T' hT')
    (Category.id_comp τ))

/-- On quasi-compact test objects the restriction map of `F` along `τ : T' ⟶ T` is the
restriction `AlgebraicGeometry.Space.GradedAlgebraRestriction.FRestrict` of classes of
quadruples. -/
theorem relativeProjFunctorEquivF_map {T T' : BigFppfOver s.site s.base s.containsBase}
    (τ : T' ⟶ T) (hT : CompactSpace ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T))
    (hT' : CompactSpace ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T'))
    (x : s.relativeProjFunctor.obj (op T)) :
    s.relativeProjFunctorEquivF T' hT' (s.relativeProjFunctor.map τ.op x) =
      s.quadrupleRestriction.FRestrict τ (s.relativeProjFunctorEquivF T hT x) := by
  refine (quadrupleSpaceEquiv_map_val_id s τ hT' x).trans ?_
  exact (congrArg _ (Category.comp_id τ).symm).trans
    ((s.quadrupleRestriction.quadrupleSpaceEquiv s.shrink.contains_relativeProj_pointAlgebra
      s.shrink.space.property.isSheaf T x).compat T T' hT hT' τ (𝟙 T)).symm

/-- **Stacks 084A, functoriality: the restriction map of `F` is the pullback of quadruples.**
For a morphism `τ : T' ⟶ T` of quasi-compact test objects and a point `x` of `F(T)` which is the
class of a quadruple `(d, f, ℒ, ψ)`, the restriction of `x` to `T'` is the class of the pullback
quadruple `(d, f ∘ τ, τ^*ℒ, τ^*ψ)`,
`AlgebraicGeometry.Space.GradedAlgebraRestriction.quadrupleRestrict`. -/
@[stacks 084A "functoriality: on quasi-compact test schemes the restriction map of F along \
h : T' -> T sends the class of a quadruple (d, f, L, psi) to the class of its pullback \
(d, f o h, h^*L, h^*psi)"]
theorem relativeProjFunctorEquivF_map_mk {T T' : BigFppfOver s.site s.base s.containsBase}
    (τ : T' ⟶ T) (hT : CompactSpace ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T))
    (hT' : CompactSpace ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T'))
    (x : s.relativeProjFunctor.obj (op T)) (f : yoneda.obj T ⟶ s.space.1) {d : ℤ} (hd : 0 < d)
    (P : (GradedAlgebraPoints.ofQuasicoherentFamily s.shrink.pointAlgebra).Quadruples T f d)
    (hx : s.relativeProjFunctorEquivF T hT x = GradedAlgebraPoints.F.mk _ f hd P) :
    s.relativeProjFunctorEquivF T' hT' (s.relativeProjFunctor.map τ.op x) =
      GradedAlgebraPoints.F.mk _ (yoneda.map τ ≫ f) hd
        (s.quadrupleRestriction.quadrupleRestrict τ f (yoneda.map τ ≫ f) rfl P) :=
  (relativeProjFunctorEquivF_map s τ hT hT' x).trans
    ((congrArg (s.quadrupleRestriction.FRestrict τ) hx).trans
      (s.quadrupleRestriction.FRestrict_mk τ f hd P))

/-- **The restriction of a point of `F(T)` to the quasi-compact opens of `T`**: the family of the
classes of quadruples `x|_V ∈ F(V)` over the quasi-compact opens `V` of the scheme of `T`. -/
def restrictCompactOpens (T : BigFppfOver s.site s.base s.containsBase)
    (x : s.relativeProjFunctor.obj (op T)) :
    SiteQcExtension.CompactOpensLimit s.quadrupleRestriction.functor T :=
  ⟨fun V => s.relativeProjFunctorEquivF _ (compactSpace_opensObject T V)
      (s.relativeProjFunctor.map (opensObjectι s.site s.base s.containsBase T V.1).op x),
    fun V V' h => (relativeProjFunctorEquivF_map s
      (GradedAlgebraRestriction.opensObjectHomOfLE T h) (compactSpace_opensObject T V)
      (compactSpace_opensObject T V') _).symm.trans
      (congrArg (s.relativeProjFunctorEquivF _ (compactSpace_opensObject T V')) (by
        rw [← FunctorToTypes.map_comp_apply, ← op_comp,
          GradedAlgebraRestriction.opensObjectHomOfLE_ι]))⟩

/-- **Stacks 084A: for an arbitrary test scheme `T`, `F(T) = lim_{V ⊆ T quasi-compact open}
F(V)`.**  The map sending a point `x` of `F(T)` to the family of its restrictions `x|_V`, read as
classes of quadruples over the quasi-compact opens `V` of `T`, is a bijection onto the families
of classes of quadruples over the quasi-compact opens which are compatible with the restrictions
`AlgebraicGeometry.Space.GradedAlgebraRestriction.FRestrict` along the inclusions. -/
@[stacks 084A "for an arbitrary test scheme T, F(T) is the limit of F(V) over the quasi-compact \
opens V of T: restricting to the quasi-compact opens is a bijection onto the compatible systems \
of classes of quadruples over them"]
theorem bijective_restrictCompactOpens (T : BigFppfOver s.site s.base s.containsBase) :
    Function.Bijective (s.restrictCompactOpens T) := by
  let e := s.quadrupleRestriction.quadrupleSpaceEquiv s.shrink.contains_relativeProj_pointAlgebra
    s.shrink.space.property.isSheaf
  have hfac : s.restrictCompactOpens T = SiteQcExtension.equivCompactOpens T ∘ e T := by
    funext x
    apply Subtype.ext
    funext V
    exact quadrupleSpaceEquiv_map_val_id s _ (compactSpace_opensObject T V) x
  rw [hfac]
  exact (SiteQcExtension.equivCompactOpens T).bijective.comp (e T).bijective

/-- On a quasi-compact test object `T` the morphism `F ⟶ X` sends a point of `F(T)` to the
`T`-point of `X` which its class of quadruples lies over. -/
theorem relativeProjπ_app_of_compactSpace (T : BigFppfOver s.site s.base s.containsBase)
    (hT : CompactSpace ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T))
    (x : s.relativeProjFunctor.obj (op T)) :
    s.relativeProjπ.app (op T) x =
      yonedaEquiv (GradedAlgebraPoints.F.point _ (s.relativeProjFunctorEquivF T hT x)) :=
  (FunctorToTypes.map_id_apply s.space.1 _).symm.trans
    (s.quadrupleRestriction.quadrupleSpaceπ_app s.shrink.contains_relativeProj_pointAlgebra
      s.shrink.space.property.isSheaf x T hT (𝟙 T))

/-- **Stacks 084A: the morphism `F ⟶ X` sends the quadruple `(d, f, ℒ, ψ)` to `f`.**  On a
quasi-compact test object `T`, a point of `F(T)` which is the class of a quadruple
`(d, f, ℒ, ψ)` is sent by `AlgebraicGeometry.Space.RelativeProjSituation.relativeProjπ` to the
`T`-point `f` of `X`. -/
@[stacks 084A "the morphism F -> X of functors sends the class of a quadruple (d, f, L, psi) \
to f"]
theorem relativeProjπ_app_mk (T : BigFppfOver s.site s.base s.containsBase)
    (hT : CompactSpace ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T))
    (x : s.relativeProjFunctor.obj (op T)) (f : yoneda.obj T ⟶ s.space.1) {d : ℤ} (hd : 0 < d)
    (P : (GradedAlgebraPoints.ofQuasicoherentFamily s.shrink.pointAlgebra).Quadruples T f d)
    (hx : s.relativeProjFunctorEquivF T hT x = GradedAlgebraPoints.F.mk _ f hd P) :
    s.relativeProjπ.app (op T) x = yonedaEquiv f :=
  (relativeProjπ_app_of_compactSpace s T hT x).trans
    (congrArg (fun ξ => yonedaEquiv (GradedAlgebraPoints.F.point _ ξ)) hx)

end RelativeProjSituation

end AlgebraicGeometry.Space

end
