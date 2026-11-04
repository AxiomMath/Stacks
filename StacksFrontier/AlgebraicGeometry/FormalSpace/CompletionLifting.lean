module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionVersality
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting

/-!
# The infinitesimal lifting property of a morphism out of a completion at a point

Let `S` be a scheme contained in a big fppf site `B`, let `V` be a scheme of the site,
`Z ⊆ |V|` and `g : V_{/Z} ⟶ W` a morphism from the completion of `V` along `Z` to an fppf sheaf
`W`. For a point `v ∈ V` we say that `g` has the *lifting property at `v`* when every small
extension `D' ⟶ D` of Artinian local rings in the site, every morphism `α : Spec D ⟶ V` over `S`
sending the closed point to `v`, with residue field finite over `κ(v)` and lying in `V_{/Z}`, and
every section `z` of `W` over `Spec D'` restricting to `g(α)`, come from a morphism
`β : Spec D' ⟶ V` lying in `V_{/Z}` extending `α` with `g(β) = z`.

This is the form of versality (Section 07XZ) that the proof of Stacks 0GI9 manipulates: it is
implied by versality (via the Rim-Schlessinger condition), it passes along étale charts, and for a
morphism to a formal spectrum it is equivalent to smoothness of the quotient stages at the
points over `v` (Tag 02HX).

## Main definitions

* `AlgebraicGeometry.FormalSpace.affineOverHom`: the morphism of the site out of
  `AlgebraicGeometry.FormalSpace.affineOver` given by a morphism of schemes over `S`.
* `AlgebraicGeometry.FormalSpace.LiftsAtCompletion`: the lifting property at a point.

## References

* [Stacks Project, Tag 0GI9](https://stacks.math.columbia.edu/tag/0GI9)
* [Stacks Project, Tag 02HX](https://stacks.math.columbia.edu/tag/02HX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] CategoryTheory.catToReflQuiver

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The morphism of the site from `Spec D`, with structure morphism `t`, to an object `V`, given
by a morphism of schemes `α : Spec D ⟶ V` over `S`. -/
def affineOverHom {D : Type u} [CommRing D] (hD : B.Contains (Spec (.of D)))
    (t : Spec (.of D) ⟶ S) {V : BigFppfOver B S hS}
    (α : Spec (.of D) ⟶ ((Over.post B.inclusion).obj V : Over S).left)
    (hα : α ≫ ((Over.post B.inclusion).obj V : Over S).hom = t) :
    affineOver B S hS hD t ⟶ V :=
  Over.homMk (ObjectProperty.homMk α) (by
    apply ObjectProperty.hom_ext
    exact hα)

/-- The underlying morphism of schemes of `affineOverHom B S hS hD t α hα` is `α`. -/
@[simp]
theorem toScheme_map_affineOverHom {D : Type u} [CommRing D] (hD : B.Contains (Spec (.of D)))
    (t : Spec (.of D) ⟶ S) {V : BigFppfOver B S hS}
    (α : Spec (.of D) ⟶ ((Over.post B.inclusion).obj V : Over S).left)
    (hα : α ≫ ((Over.post B.inclusion).obj V : Over S).hom = t) :
    (BigFppfOver.toScheme B S hS).map (affineOverHom B S hS hD t α hα) = α := rfl

/-- **The lifting property of `g : V_{/Z} ⟶ W` at a point `v` of `V`.** For every small
extension `φ : D' ⟶ D` of Artinian local rings whose spectra lie in the site, every morphism
`α : Spec D ⟶ V` over `S` sending the closed point to `v`, with `κ(α(𝔪)) ⟶ κ(𝔪)` finite and
lying in `V_{/Z}`, and every section `z` of `W` over `Spec D'` restricting to `g(α)`, there is a
morphism `β : Spec D' ⟶ V` over `S` lying in `V_{/Z}`, with `Spec φ ≫ β = α` and `g(β) = z`. -/
def LiftsAtCompletion (V : BigFppfOver B S hS)
    (Z : Set (Space.points B S hS (yoneda.obj V))) (W : FppfSheaf B S hS)
    (g : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ W)
    (v : ((Over.post B.inclusion).obj V : Over S).left) : Prop :=
  ∀ ⦃D' D : CommRingCat.{u}⦄ (φ : D' ⟶ D), InfinitesimalLifting.IsSmallExtension φ →
    ∀ [IsLocalRing D] (hD : B.Contains (Spec (.of D))) (hD' : B.Contains (Spec (.of D')))
      (s : Spec (.of D') ⟶ S)
      (α : Spec (.of D) ⟶ ((Over.post B.inclusion).obj V : Over S).left)
      (hα : α ≫ ((Over.post B.inclusion).obj V : Over S).hom = Spec.map φ ≫ s),
      α.base (IsLocalRing.closedPoint D) = v →
      (α.residueFieldMap (IsLocalRing.closedPoint D)).hom.Finite →
      ∀ (ha : Space.HasImageIn B S hS (yoneda.obj V) Z
          (affineOver B S hS hD (Spec.map φ ≫ s)) (affineOverHom B S hS hD _ α hα))
        (z : W.obj.obj (op (affineOver B S hS hD' s))),
        W.obj.map (affineOverHom B S hS hD (Spec.map φ ≫ s) (V := affineOver B S hS hD' s)
          (Spec.map φ) rfl).op z =
          g.hom.app _ (presheafSection B S hS _ ha) →
        ∃ (β : Spec (.of D') ⟶ ((Over.post B.inclusion).obj V : Over S).left)
          (hβ : β ≫ ((Over.post B.inclusion).obj V : Over S).hom = s)
          (hb : Space.HasImageIn B S hS (yoneda.obj V) Z
            (affineOver B S hS hD' s) (affineOverHom B S hS hD' s β hβ)),
          Spec.map φ ≫ β = α ∧ g.hom.app _ (presheafSection B S hS _ hb) = z

/-- A section has point-set image in the inverse image of `T` exactly when its image under the
morphism has point-set image in `T`. -/
theorem hasImageIn_preimage_iff {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (T : Set (Space.points B S hS X)) (U : BigFppfOver B S hS) (x : X'.obj (op U)) :
    Space.HasImageIn B S hS X' (Space.pointsMap B S hS X' f ⁻¹' T) U x ↔
      Space.HasImageIn B S hS X T U (f.app (op U) x) := by
  have key : ∀ p : Space.FieldValuedPoint B S hS (yoneda.obj U),
      Space.pointsMap B S hS X' f
        ((⟨p.carrier, p.contained, p.toBase, X'.map p.value.op x⟩ :
          Space.FieldValuedPoint B S hS X').class B S hS X') =
      (⟨p.carrier, p.contained, p.toBase, X.map p.value.op (f.app (op U) x)⟩ :
          Space.FieldValuedPoint B S hS X).class B S hS X := by
    intro p
    rw [Space.pointsMap_class]
    congr 1
    exact congrArg (fun w => (⟨p.carrier, p.contained, p.toBase, w⟩ :
      Space.FieldValuedPoint B S hS X)) (NatTrans.naturality_apply f p.value.op x)
  refine ⟨fun h p => ?_, fun h p => ?_⟩
  · rw [← key]
    exact h p
  · rw [Set.mem_preimage, key]
    exact h p

/-- The spectrum of an Artinian local ring has only its closed point. -/
theorem eq_closedPoint_of_isArtinianRing (D : CommRingCat.{u}) [IsLocalRing D] [IsArtinianRing D]
    (y : Spec D) : y = IsLocalRing.closedPoint D := by
  have := y.isPrime
  exact PrimeSpectrum.ext
    (IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime y.asIdeal))

/-- Followed by an open immersion, a morphism with finite residue field map at a point still has
a finite residue field map there. -/
private theorem finite_residueFieldMap_comp_of_isOpenImmersion {X Y Z : Scheme.{u}} (α : X ⟶ Y)
    (f : Y ⟶ Z) [IsOpenImmersion f] (x : X) (h : (α.residueFieldMap x).hom.Finite) :
    ((α ≫ f).residueFieldMap x).hom.Finite := by
  rw [Scheme.residueFieldMap_comp]
  exact RingHom.Finite.comp h (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (f.residueFieldMap (α.base x))).2)

/-- If `Spec φ ≫ β' = α ≫ f` for a surjection `φ : D' ⟶ D` of local rings with `D'` Artinian,
then the image of `β'` lies in the image of `f`. -/
private theorem range_subset_range_of_isArtinianRing {D' D : CommRingCat.{u}} [IsLocalRing D']
    [IsArtinianRing D'] [IsLocalRing D] (φ : D' ⟶ D) (hφ : Function.Surjective φ.hom)
    {X Y : Scheme.{u}} (β' : Spec D' ⟶ X) (α : Spec D ⟶ Y) (f : Y ⟶ X)
    (h : Spec.map φ ≫ β' = α ≫ f) : Set.range β'.base ⊆ Set.range f.base := by
  rintro _ ⟨y, rfl⟩
  have hy : y = (Spec.map φ).base (IsLocalRing.closedPoint D) := by
    rw [eq_closedPoint_of_isArtinianRing D' y]
    have : IsLocalHom φ.hom := IsLocalHom.of_surjective φ.hom hφ
    exact (Spec_closedPoint (f := φ)).symm
  refine ⟨α.base (IsLocalRing.closedPoint D), ?_⟩
  rw [hy]
  show (α ≫ f).base (IsLocalRing.closedPoint D) =
    (Spec.map φ ≫ β').base (IsLocalRing.closedPoint D)
  rw [h]

/-- **The lifting property passes to the completion of an open subscheme.** For an open
immersion `j : U ⟶ V` of the site, if `G : V_{/Z} ⟶ W` has the lifting property at `j(u)`, then
`G` precomposed with `j_{/Z} : U_{/j⁻¹Z} ⟶ V_{/Z}` has it at `u`. -/
theorem liftsAtCompletion_comp_completionSheafMap {U V : BigFppfOver B S hS} (j : U ⟶ V)
    [IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (Z : Set (Space.points B S hS (yoneda.obj V))) (W : FppfSheaf B S hS)
    (G : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ W)
    (u : ((Over.post B.inclusion).obj U : Over S).left)
    (hG : LiftsAtCompletion B S hS V Z W G ((BigFppfOver.toScheme B S hS).map j u)) :
    LiftsAtCompletion B S hS U (Space.pointsMap B S hS (yoneda.obj U) (yoneda.map j) ⁻¹' Z) W
      (Space.completionSheafMap B S hS (yoneda.map j) Z ≫ G) u := by
  intro D' D φ hφ _ hD hD' s α hα hpt hfin ha z hz
  let jS : ((Over.post B.inclusion).obj U : Over S).left ⟶
      ((Over.post B.inclusion).obj V : Over S).left := ((Over.post B.inclusion).map j).left
  have : IsOpenImmersion jS :=
    inferInstanceAs (IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j))
  have hj : jS ≫ ((Over.post B.inclusion).obj V : Over S).hom =
      ((Over.post B.inclusion).obj U : Over S).hom := Over.w ((Over.post B.inclusion).map j)
  have hα' : (α ≫ jS) ≫
      ((Over.post B.inclusion).obj V : Over S).hom = Spec.map φ ≫ s :=
    (Category.assoc _ _ _).trans ((congrArg (α ≫ ·) hj).trans hα)
  have hpt' : (α ≫ jS).base (IsLocalRing.closedPoint D) =
      jS u := by
    show jS.base (α.base _) = _
    rw [hpt]
  have hfin' : ((α ≫ jS).residueFieldMap (IsLocalRing.closedPoint D)).hom.Finite :=
    finite_residueFieldMap_comp_of_isOpenImmersion α jS _ hfin
  have ha' := (hasImageIn_preimage_iff B S hS (yoneda.map j) Z _ _).mp ha
  have hz' : W.obj.map (affineOverHom B S hS hD (Spec.map φ ≫ s) (V := affineOver B S hS hD' s)
      (Spec.map φ) rfl).op z = G.hom.app _ (presheafSection B S hS _ ha') := by
    rw [hz]
    exact congrArg (G.hom.app _)
      (completionSheafMap_presheafSection B S hS (yoneda.map j) Z _ ha ha')
  obtain ⟨β', hβ', hb', h1', h2'⟩ := hG φ hφ hD hD' s _ hα' hpt' hfin' ha' z hz'
  obtain ⟨_, -, _, -, hsurj, -⟩ := hφ
  let β := IsOpenImmersion.lift jS β'
    (range_subset_range_of_isArtinianRing φ hsurj β' α jS h1')
  have hβj : β ≫ jS = β' := IsOpenImmersion.lift_fac _ _ _
  have hβ : β ≫ ((Over.post B.inclusion).obj U : Over S).hom = s := by
    rw [← hj, ← Category.assoc, hβj, hβ']
  have hcompb : affineOverHom B S hS hD' s β hβ ≫ j = affineOverHom B S hS hD' s β' hβ' := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hβj
  have hb : Space.HasImageIn B S hS (yoneda.obj U)
      (Space.pointsMap B S hS (yoneda.obj U) (yoneda.map j) ⁻¹' Z)
      (affineOver B S hS hD' s) (affineOverHom B S hS hD' s β hβ) :=
    (hasImageIn_preimage_iff B S hS (yoneda.map j) Z _ _).mpr (by rwa [← hcompb] at hb')
  refine ⟨β, hβ, hb, ?_, ?_⟩
  · rw [← cancel_mono jS, Category.assoc, hβj, h1']
  · have hx' : Space.HasImageIn B S hS (yoneda.obj V) Z (affineOver B S hS hD' s)
        ((yoneda.map j).app (op (affineOver B S hS hD' s)) (affineOverHom B S hS hD' s β hβ)) :=
      (hasImageIn_preimage_iff B S hS (yoneda.map j) Z _ _).mp hb
    have h3 := completionSheafMap_presheafSection B S hS (yoneda.map j) Z
      (affineOverHom B S hS hD' s β hβ) hb hx'
    refine ((congrArg (G.hom.app _) h3).trans ?_).trans h2'
    exact congrArg (G.hom.app _) (by congr 1)

end AlgebraicGeometry.FormalSpace
