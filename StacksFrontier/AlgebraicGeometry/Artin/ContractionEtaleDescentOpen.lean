module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorsWithEquivariantMap

/-!
# Étale descent of a morphism out of an open subspace cut out by a set of points

Let `{V_i ⟶ V}` be a family of objects of the big fppf site over `S` which generates a
covering sieve, let `W` be a set of points of `V` and let `W_i` be its inverse image in `V_i`.
The open subspaces `V_i|_{W_i}` are *not* objects of the site, so the fppf sheaf condition
cannot be applied to the family `{V_i|_{W_i} ⟶ V|_W}` directly. This file proves that it can
be applied all the same: the family generates a covering sieve of sections of `V|_W` at every
object of the site, so a morphism from `V|_W` into an fppf sheaf is glued from, and determined
by, its restrictions to the `V_i|_{W_i}`.

For `W` the complement of a closed subset `Z ⊆ |V|` this is the descent of the second
component `u' : V ∖ Z ⟶ U'` of a section of Artin's contraction functor along an étale
covering.

## Main results

* `AlgebraicGeometry.LocallyNoetherianOver.ofArrows_mem_topology_of_isCovering`: a covering
  family of the locally Noetherian site over `S` generates a covering sieve of the big fppf
  site over `S`.
* `AlgebraicGeometry.Space.exists_lift_of_ofArrows_mem_topology`: a section of `V` over an
  object of the site lifts, on a covering sieve, to a section of one of the `V_i`.
* `AlgebraicGeometry.Space.familyImage_sieveOfSection_mem_openSubspaceOfPoints`: the family of
  open subspaces `{V_i|_{W_i} ⟶ V|_W}` generates a covering sieve of sections of `V|_W`, for
  any set of points `W`.
* `AlgebraicGeometry.Space.compatible_of_overlap_openSubspaceOfPoints`: agreement of the two
  restrictions to the overlaps `V_i ×_V V_j` implies the compatibility hypothesis of
  `AlgebraicGeometry.Space.glueHom`, which quantifies over all objects of the site.
* `AlgebraicGeometry.Space.glueHom_openSubspaceOfPoints` and
  `AlgebraicGeometry.Space.hom_ext_openSubspaceOfPoints`: a morphism from `V|_W` into an fppf
  sheaf is glued from, and determined by, its restrictions.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 0GHG](https://stacks.math.columbia.edu/tag/0GHG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace LocallyNoetherianOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A covering family of the locally Noetherian site over `S` generates a covering sieve of
the big fppf site over `S`. -/
theorem ofArrows_mem_topology_of_isCovering
    {E : Covering (LocallyNoetherianOver B S hS)} (hE : IsCovering B S hS E) :
    Sieve.ofArrows (fun i => (E.2.X i).obj) (fun i => (E.2.f i).hom) ∈
      BigFppfOver.topology B S hS E.1.obj := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck
    ⟨(E.2.map (toBigFppfOver B S hS)).map (BigFppfOver.forget B S hS), rfl, hE⟩

end LocallyNoetherianOver

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A section `b` of `X` lies in the open subspace cut out by the inverse image of `W` under
`f : X ⟶ Y` as soon as `b ≫ f` lies in the open subspace of `Y` cut out by `W`. -/
private theorem mem_openSubspaceOfPoints_of_comp_mem {X Y : BigFppfOver B S hS} (f : X ⟶ Y)
    {W : Set (points B S hS (yoneda.obj Y))} {Wx : Set (points B S hS (yoneda.obj X))}
    (hWx : Wx = pointsMap B S hS (yoneda.obj X) (yoneda.map f) ⁻¹' W)
    {T : BigFppfOver B S hS} (b : T ⟶ X)
    (hb : b ≫ f ∈ (openSubspaceOfPoints B S hS (yoneda.obj Y) W).obj (Opposite.op T)) :
    b ∈ (openSubspaceOfPoints B S hS (yoneda.obj X) Wx).obj (Opposite.op T) := by
  rw [hWx, ← preimage_openSubspaceOfPoints']
  exact hb

/-- **A section lifts along a covering family on a covering sieve.** If `{V_i ⟶ V}` generates
a covering sieve of the big fppf site over `S`, then for every section `a : T ⟶ V` there is a
covering sieve of `T` each of whose arrows `g` makes `g ≫ a` factor through some `V_i`. -/
theorem exists_lift_of_ofArrows_mem_topology {V : BigFppfOver B S hS} {I : Type*}
    (Vi : I → BigFppfOver B S hS) (f : ∀ i, Vi i ⟶ V)
    (hf : Sieve.ofArrows Vi f ∈ BigFppfOver.topology B S hS V)
    {T : BigFppfOver B S hS} (a : T ⟶ V) :
    ∃ R ∈ BigFppfOver.topology B S hS T, ∀ ⦃T' : BigFppfOver B S hS⦄ ⦃g : T' ⟶ T⦄,
      R.arrows g → ∃ (i : I) (b : T' ⟶ Vi i), b ≫ f i = g ≫ a := by
  refine ⟨Sieve.pullback a (Sieve.ofArrows Vi f),
    (BigFppfOver.topology B S hS).pullback_stable a hf, ?_⟩
  rintro T' g ⟨_, h, _, ⟨i⟩, hcomp⟩
  exact ⟨i, h, hcomp⟩

/-- **The open subspaces cut out by inverse images of a set of points cover.** Let `{V_i ⟶ V}`
generate a covering sieve of the big fppf site over `S`, let `W` be a set of points of `V` and let
`W_i` be its inverse image in `V_i`. Then the family of open subspaces `{V_i|_{W_i} ⟶ V|_W}`
generates a covering sieve of sections of `V|_W` at every object of the site.

Taking `W` to be the complement of a closed subset `Z ⊆ |V|` and `W_i` the complement of its
inverse image, this says that `{V_i ∖ Z_i ⟶ V ∖ Z}` is an fppf covering of the subfunctor
`V ∖ Z`. -/
theorem familyImage_sieveOfSection_mem_openSubspaceOfPoints {V : BigFppfOver B S hS}
    {I : Type*} (Vi : I → BigFppfOver B S hS) (f : ∀ i, Vi i ⟶ V)
    (hf : Sieve.ofArrows Vi f ∈ BigFppfOver.topology B S hS V)
    (W : Set (points B S hS (yoneda.obj V)))
    (Wi : ∀ i, Set (points B S hS (yoneda.obj (Vi i))))
    (hWi : ∀ i, Wi i = pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' W)
    (T : BigFppfOver B S hS)
    (x : (openSubspaceOfPoints B S hS (yoneda.obj V) W).toFunctor.obj (Opposite.op T)) :
    (familyImage fun i => openSubspaceOfPointsRestrict B S hS (yoneda.map (f i)) (Wi i) W
        (hWi i).subset).sieveOfSection x ∈ BigFppfOver.topology B S hS T := by
  obtain ⟨R, hR, hlift⟩ :=
    exists_lift_of_ofArrows_mem_topology B S hS Vi f hf (T := T) x.1
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hR
  intro T' g hg
  obtain ⟨i, b, hb⟩ := hlift hg
  have hbmem := mem_openSubspaceOfPoints_of_comp_mem B S hS (f i) (hWi i) b
    (hb ▸ (openSubspaceOfPoints B S hS (yoneda.obj V) W).map g.op x.2)
  exact ⟨i, ⟨b, hbmem⟩, Subtype.ext hb⟩

/-- **Agreement on overlaps gives the glueing compatibility.** If the objects `P i j` of the
site receive two morphisms `pr₁ i j`, `pr₂ i j` through which every pair of morphisms
`a : Y ⟶ V_i`, `b : Y ⟶ V_j` agreeing over `V` factors, and the restrictions of `φ i` and `φ j`
to the open subspace of `P i j` cut out by the inverse image of `W` agree, then `φ i` and `φ j`
agree on any two sections of `V_i|_{W_i}` and `V_j|_{W_j}` with the same image in `V|_W`, over
every object of the big fppf site. No hypothesis is made on `Q`. -/
theorem compatible_of_overlap_openSubspaceOfPoints {V : BigFppfOver B S hS} {I : Type*}
    (Vi : I → BigFppfOver B S hS) (f : ∀ i, Vi i ⟶ V)
    (W : Set (points B S hS (yoneda.obj V)))
    (Wi : ∀ i, Set (points B S hS (yoneda.obj (Vi i))))
    (hWi : ∀ i, Wi i = pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' W)
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (φ : ∀ i, (openSubspaceOfPoints B S hS (yoneda.obj (Vi i)) (Wi i)).toFunctor ⟶ Q)
    (P : I → I → BigFppfOver B S hS) (pr₁ : ∀ i j, P i j ⟶ Vi i) (pr₂ : ∀ i j, P i j ⟶ Vi j)
    (Wij : ∀ i j, Set (points B S hS (yoneda.obj (P i j))))
    (hWij₁ : ∀ i j, Wij i j =
      pointsMap B S hS (yoneda.obj (P i j)) (yoneda.map (pr₁ i j)) ⁻¹' Wi i)
    (hWij₂ : ∀ i j, Wij i j =
      pointsMap B S hS (yoneda.obj (P i j)) (yoneda.map (pr₂ i j)) ⁻¹' Wi j)
    (hlift : ∀ (i j : I) (Y : BigFppfOver B S hS) (a : Y ⟶ Vi i) (b : Y ⟶ Vi j),
      a ≫ f i = b ≫ f j → ∃ h : Y ⟶ P i j, h ≫ pr₁ i j = a ∧ h ≫ pr₂ i j = b)
    (hagree : ∀ i j,
      openSubspaceOfPointsRestrict B S hS (yoneda.map (pr₁ i j)) (Wij i j) (Wi i)
          (hWij₁ i j).subset ≫ φ i =
        openSubspaceOfPointsRestrict B S hS (yoneda.map (pr₂ i j)) (Wij i j) (Wi j)
          (hWij₂ i j).subset ≫ φ j) :
    ∀ (Y : (BigFppfOver B S hS)ᵒᵖ) (i j : I)
      (y : (openSubspaceOfPoints B S hS (yoneda.obj (Vi i)) (Wi i)).toFunctor.obj Y)
      (y' : (openSubspaceOfPoints B S hS (yoneda.obj (Vi j)) (Wi j)).toFunctor.obj Y),
      (openSubspaceOfPointsRestrict B S hS (yoneda.map (f i)) (Wi i) W (hWi i).subset).app Y y =
        (openSubspaceOfPointsRestrict B S hS (yoneda.map (f j)) (Wi j) W
          (hWi j).subset).app Y y' →
        (φ i).app Y y = (φ j).app Y y' := by
  intro Y
  obtain ⟨T⟩ := Y
  intro i j y y' hy
  have hcomm : y.1 ≫ f i = y'.1 ≫ f j := congrArg Subtype.val hy
  obtain ⟨h, h₁, h₂⟩ := hlift i j T y.1 y'.1 hcomm
  have hmem := mem_openSubspaceOfPoints_of_comp_mem B S hS (pr₁ i j) (hWij₁ i j) h
    (h₁ ▸ y.2)
  have hy₁ : (openSubspaceOfPointsRestrict B S hS (yoneda.map (pr₁ i j)) (Wij i j) (Wi i)
      (hWij₁ i j).subset).app (Opposite.op T) ⟨h, hmem⟩ = y := Subtype.ext h₁
  have hy₂ : (openSubspaceOfPointsRestrict B S hS (yoneda.map (pr₂ i j)) (Wij i j) (Wi j)
      (hWij₂ i j).subset).app (Opposite.op T) ⟨h, hmem⟩ = y' := Subtype.ext h₂
  rw [← hy₁, ← hy₂]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (hagree i j) (Opposite.op T)) ⟨h, hmem⟩

/-- **Glueing a morphism out of an open subspace cut out by a set of points.** A compatible
family of morphisms `V_i|_{W_i} ⟶ Q` into an fppf sheaf comes from a unique morphism
`V|_W ⟶ Q`. -/
theorem glueHom_openSubspaceOfPoints {V : BigFppfOver B S hS} {I : Type*}
    (Vi : I → BigFppfOver B S hS) (f : ∀ i, Vi i ⟶ V)
    (hf : Sieve.ofArrows Vi f ∈ BigFppfOver.topology B S hS V)
    (W : Set (points B S hS (yoneda.obj V)))
    (Wi : ∀ i, Set (points B S hS (yoneda.obj (Vi i))))
    (hWi : ∀ i, Wi i = pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' W)
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q)
    (φ : ∀ i, (openSubspaceOfPoints B S hS (yoneda.obj (Vi i)) (Wi i)).toFunctor ⟶ Q)
    (hφ : ∀ (Z : (BigFppfOver B S hS)ᵒᵖ) (i j : I)
      (y : (openSubspaceOfPoints B S hS (yoneda.obj (Vi i)) (Wi i)).toFunctor.obj Z)
      (y' : (openSubspaceOfPoints B S hS (yoneda.obj (Vi j)) (Wi j)).toFunctor.obj Z),
      (openSubspaceOfPointsRestrict B S hS (yoneda.map (f i)) (Wi i) W (hWi i).subset).app Z y =
        (openSubspaceOfPointsRestrict B S hS (yoneda.map (f j)) (Wi j) W
          (hWi j).subset).app Z y' →
        (φ i).app Z y = (φ j).app Z y') :
    ∃! ψ : (openSubspaceOfPoints B S hS (yoneda.obj V) W).toFunctor ⟶ Q,
      ∀ i, openSubspaceOfPointsRestrict B S hS (yoneda.map (f i)) (Wi i) W (hWi i).subset ≫
        ψ = φ i :=
  glueHom _ _
    (familyImage_sieveOfSection_mem_openSubspaceOfPoints B S hS Vi f hf W Wi hWi) hQ φ hφ

/-- **A morphism out of an open subspace is determined by its restrictions.** -/
theorem hom_ext_openSubspaceOfPoints {V : BigFppfOver B S hS} {I : Type*}
    (Vi : I → BigFppfOver B S hS) (f : ∀ i, Vi i ⟶ V)
    (hf : Sieve.ofArrows Vi f ∈ BigFppfOver.topology B S hS V)
    (W : Set (points B S hS (yoneda.obj V)))
    (Wi : ∀ i, Set (points B S hS (yoneda.obj (Vi i))))
    (hWi : ∀ i, Wi i = pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' W)
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q)
    (ψ ψ' : (openSubspaceOfPoints B S hS (yoneda.obj V) W).toFunctor ⟶ Q)
    (hψ : ∀ i, openSubspaceOfPointsRestrict B S hS (yoneda.map (f i)) (Wi i) W
      (hWi i).subset ≫ ψ =
        openSubspaceOfPointsRestrict B S hS (yoneda.map (f i)) (Wi i) W (hWi i).subset ≫ ψ') :
    ψ = ψ' :=
  hom_ext_of_familyImage_cover _ _
    (familyImage_sieveOfSection_mem_openSubspaceOfPoints B S hS Vi f hf W Wi hWi) hQ ψ ψ' hψ

end Space

end AlgebraicGeometry

end
