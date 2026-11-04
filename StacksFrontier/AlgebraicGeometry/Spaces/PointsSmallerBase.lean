module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Points of an algebraic space and a change of base scheme (Stacks 03BU, 03BX, 03HI)

Let `h : W ⟶ S` be a morphism of a big fppf site and let `Λ_h` be the lower-shriek extension
`CategoryTheory.OverShriek.relocalizePresheafFunctor h` of Stacks 03I5 part (2), which carries a
presheaf on the big fppf site of `W` to one on the big fppf site of `S`.

This file proves that **the point set of Stacks 03BU and the topology of Stacks 03BX are unchanged
by `Λ_h`**: the points of `Λ_h F` over `S` are the points of `F` over `W`, by a homeomorphism, and
the comparison is natural in `F`. Consequently closedness on points (**Stacks 03HI** part (1)) of a
morphism of presheaves on the site of `W` is inherited from its extension, which is the step the
universally closed clause of Stacks 03ZM needs in order to be read over two bases.

A field-valued point of `Λ_h F` over `S` is a field spectrum in the site, a structure morphism to
`S`, and a section of `Λ_h F` over the resulting object — and such a section is a factorization
`ψ` of that structure morphism through `W` together with a section of `F` over `(Spec K, ψ)`. So
the data is exactly a field-valued point of `F` over `W`: the factorization `ψ` *is* the structure
morphism to `W`, and the structure morphism to `S` it determines carries no information.

## Main definitions

* `AlgebraicGeometry.Space.FieldValuedPoint.relocalize` and `.derelocalize`: the two readings of a
  field-valued point.
* `AlgebraicGeometry.Space.pointsRelocalize`: the induced map on points.
* `AlgebraicGeometry.Space.FieldValuedPoint.relocalizeRep` and `.derelocalizeRep`: the two
  readings of a field-valued point of a representable presheaf.

## Main results

* `AlgebraicGeometry.Space.pointsRelocalize_bijective`: **Stacks 03BU** is unchanged by the
  lower-shriek extension.
* `AlgebraicGeometry.Space.isOpen_pointsRelocalize_iff`: **Stacks 03BX** is unchanged by it.
* `AlgebraicGeometry.Space.isClosedMap_pointsRelocalize` and
  `AlgebraicGeometry.Space.continuous_pointsRelocalize`: the comparison is a homeomorphism.
* `AlgebraicGeometry.Space.isClosedMorphism_of_relocalizeMap`: **Stacks 03HI** part (1) is
  inherited from the lower-shriek extension.

## Implementation notes

Injectivity and surjectivity of the comparison on points are both proved by exhibiting a
field-valued extension, never by substituting one structure morphism for another: the structure
morphism to `S` occurs in the *type* of the section a field-valued point carries, so `subst` fails
the occurs check and `rw` reports `motive is not type correct`. Each comparison is instead the
morphism of the site which is the identity on the underlying field spectrum, and the two sections
agree by `CategoryTheory.OverShriek.sigmaMk_eq` or its identity case; the one place where the
structure morphism has to be moved under an equality,
`AlgebraicGeometry.Space.class_relocalize_map_derelocalizeRep`, supplies the equality as a term
rather than rewriting with it.

The topology is the one detected by scheme-valued points, so the comparison of topologies is the
comparison of the two indexing families. Every scheme-valued point of `Λ_h F` is the extension of
one of `F` up to an isomorphism of the site which is the identity on underlying schemes
(`AlgebraicGeometry.exists_relocalizeChart` and `AlgebraicGeometry.relocalizeBaseHom`), the two
objects have the *same* underlying scheme, and corresponding scheme-valued points have the same
underlying scheme point — so the two families cut out the same subsets of the same scheme.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

namespace Space

variable (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u)

/-! ### Field-valued points of a lower-shriek extension -/

/-- A field-valued point of `F` over `W`, read as a field-valued point of `Λ_h F` over `S`. -/
noncomputable def FieldValuedPoint.relocalize (p : FieldValuedPoint B W hW F) :
    FieldValuedPoint B S hS ((OverShriek.relocalizePresheafFunctor h).obj F) where
  carrier := p.carrier
  field := p.field
  contained := p.contained
  toBase := p.toBase ≫ h.hom
  value := OverShriek.relocalizeMk h F
    (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hW) p.value rfl

/-- A field-valued point of `Λ_h F` over `S`, read as a field-valued point of `F` over `W`: its
section carries a factorization of the structure morphism through `W`, which is the structure
morphism to take, and a section of `F` over it. -/
noncomputable def FieldValuedPoint.derelocalize
    (q : FieldValuedPoint B S hS ((OverShriek.relocalizePresheafFunctor h).obj F)) :
    FieldValuedPoint B W hW F where
  carrier := q.carrier
  field := q.field
  contained := q.contained
  toBase := (q.value.1.1).hom
  value := q.value.1.2

/-- The factorization and section carried by the restriction of the reading of `p` along a morphism
`f` of field spectra over `S` are the restriction of `p.value` along any `g` with the same
underlying morphism. -/
private theorem relocalize_map_value_val (p : FieldValuedPoint B W hW F)
    {r : FieldValuedPoint B S hS ((OverShriek.relocalizePresheafFunctor h).obj F)}
    (f : r.siteObject ⟶ (FieldValuedPoint.relocalize B W S hW hS h F p).siteObject)
    {ψ : B.obj r.contained ⟶ B.obj hW}
    (g : (Over.mk ψ : BigFppfOver B W hW) ⟶ Over.mk (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hW))
    (hg : f.left = g.left) :
    (((OverShriek.relocalizePresheafFunctor h).obj F).map f.op
        (FieldValuedPoint.relocalize B W S hW hS h F p).value).1 = ⟨ψ, F.map g.op p.value⟩ :=
  OverShriek.sigmaMk_eq F p.value _ g hg

/-- Being a field-valued extension is preserved by reading a point over the larger base. -/
theorem FieldValuedPoint.dominates_relocalize {r p : FieldValuedPoint B W hW F}
    (hd : FieldValuedPoint.Dominates B W hW F r p) :
    FieldValuedPoint.Dominates B S hS ((OverShriek.relocalizePresheafFunctor h).obj F)
      (FieldValuedPoint.relocalize B W S hW hS h F r)
      (FieldValuedPoint.relocalize B W S hW hS h F p) := by
  obtain ⟨f, hf⟩ := hd
  have hw : f.left.hom ≫ p.toBase = r.toBase := congrArg (fun k => k.hom) (Over.w f)
  refine ⟨Over.homMk f.left (by
    ext
    have hbase : f.left.hom ≫ p.toBase ≫ h.hom = r.toBase ≫ h.hom := by
      rw [← hw, Category.assoc]
    exact hbase), Subtype.ext ((relocalize_map_value_val B W S hW hS h F p
      (r := FieldValuedPoint.relocalize B W S hW hS h F r) _ f rfl).trans ?_)⟩
  exact Sigma.ext rfl (heq_of_eq hf)

/-- A field-valued extension over the larger base of the reading of `p` is, read back over `W`,
a field-valued extension of `p`. The factorization its section carries is the comparison. -/
theorem FieldValuedPoint.dominates_derelocalize
    {q : FieldValuedPoint B S hS ((OverShriek.relocalizePresheafFunctor h).obj F)}
    {p : FieldValuedPoint B W hW F}
    (hd : FieldValuedPoint.Dominates B S hS
      ((OverShriek.relocalizePresheafFunctor h).obj F) q
      (FieldValuedPoint.relocalize B W S hW hS h F p)) :
    FieldValuedPoint.Dominates B W hW F
      (FieldValuedPoint.derelocalize B W S hW hS h F q) p := by
  obtain ⟨f', hf'⟩ := hd
  have hfst : f'.left ≫ (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hW) = q.value.1.1 :=
    congrArg Sigma.fst
      ((relocalize_map_value_val B W S hW hS h F p f' (Over.homMk f'.left rfl) rfl).symm.trans
        (congrArg Subtype.val hf'))
  refine ⟨Over.homMk f'.left hfst, ?_⟩
  exact eq_of_heq (Sigma.mk.inj
    ((relocalize_map_value_val B W S hW hS h F p f' (Over.homMk f'.left hfst) rfl).symm.trans
      (congrArg Subtype.val hf'))).2

/-- A field-valued extension of a field-valued point has the same class. -/
private theorem class_eq_class_of_dominates {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p q : FieldValuedPoint B S hS G} (hd : FieldValuedPoint.Dominates B S hS G p q) :
    p.class B S hS G = q.class B S hS G :=
  FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS G
    ⟨p, FieldValuedPoint.dominates_refl B S hS G p, hd⟩

/-- Reading a field-valued point of `Λ_h F` over `W` and then back over `S` gives a field-valued
extension of it: the comparison is the identity on the underlying field spectrum. -/
theorem FieldValuedPoint.dominates_relocalize_derelocalize
    (q : FieldValuedPoint B S hS ((OverShriek.relocalizePresheafFunctor h).obj F)) :
    FieldValuedPoint.Dominates B S hS ((OverShriek.relocalizePresheafFunctor h).obj F)
      (FieldValuedPoint.relocalize B W S hW hS h F
        (FieldValuedPoint.derelocalize B W S hW hS h F q)) q := by
  have hb : (q.value.1.1).hom ≫ h.hom = q.toBase := congrArg (fun k => k.hom) q.value.2
  refine ⟨Over.homMk (𝟙 (B.obj q.contained)) (by
    ext
    have hbase : 𝟙 _ ≫ q.toBase = (q.value.1.1).hom ≫ h.hom := by
      rw [hb, Category.id_comp]
    exact hbase), Subtype.ext (OverShriek.sigmaMk_eq_self F q.value.1.2 _ rfl)⟩

/-! ### Points of a lower-shriek extension -/

/-- **The points of a lower-shriek extension are the points of the original presheaf.** The map
reads a field-valued point of `F` over `W` as one of `Λ_h F` over `S`. -/
noncomputable def pointsRelocalize :
    points B W hW F → points B S hS ((OverShriek.relocalizePresheafFunctor h).obj F) :=
  Quot.map (FieldValuedPoint.relocalize B W S hW hS h F)
    (fun _ _ hpq => by
      obtain ⟨r, h₁, h₂⟩ := hpq
      exact ⟨FieldValuedPoint.relocalize B W S hW hS h F r,
        FieldValuedPoint.dominates_relocalize B W S hW hS h F h₁,
        FieldValuedPoint.dominates_relocalize B W S hW hS h F h₂⟩)

/-- The point of `Λ_h F` over `S` determined by a field-valued point `p` of `F` over `W` is the
class of `p` read over `S`. -/
@[simp]
theorem pointsRelocalize_class (p : FieldValuedPoint B W hW F) :
    pointsRelocalize B W S hW hS h F (p.class B W hW F) =
      (FieldValuedPoint.relocalize B W S hW hS h F p).class B S hS _ := rfl

/-- The map `pointsRelocalize` from the points of `F` over `W` to those of `Λ_h F` over `S` is
injective. -/
theorem pointsRelocalize_injective : Function.Injective (pointsRelocalize B W S hW hS h F) := by
  intro x y hxy
  induction x using Quot.ind with | _ p =>
  induction y using Quot.ind with | _ p' =>
  obtain ⟨r, h₁, h₂⟩ := (FieldValuedPoint.class_eq_class_iff B S hS _ _ _).1 hxy
  exact FieldValuedPoint.class_eq_class_of_hasCommonExtension B W hW F
    ⟨FieldValuedPoint.derelocalize B W S hW hS h F r,
      FieldValuedPoint.dominates_derelocalize B W S hW hS h F h₁,
      FieldValuedPoint.dominates_derelocalize B W S hW hS h F h₂⟩

/-- The map `pointsRelocalize` from the points of `F` over `W` to those of `Λ_h F` over `S` is
surjective. -/
theorem pointsRelocalize_surjective : Function.Surjective (pointsRelocalize B W S hW hS h F) := by
  intro y
  induction y using Quot.ind with | _ q =>
  exact ⟨(FieldValuedPoint.derelocalize B W S hW hS h F q).class B W hW F,
    class_eq_class_of_dominates B S hS
      (FieldValuedPoint.dominates_relocalize_derelocalize B W S hW hS h F q)⟩

/-- The map `pointsRelocalize` from the points of `F` over `W` to those of `Λ_h F` over `S` is
bijective. -/
theorem pointsRelocalize_bijective : Function.Bijective (pointsRelocalize B W S hW hS h F) :=
  ⟨pointsRelocalize_injective B W S hW hS h F, pointsRelocalize_surjective B W S hW hS h F⟩

/-- Reading a point over the larger base is natural in the presheaf. -/
theorem pointsRelocalize_naturality {F G : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (k : F ⟶ G)
    (x : points B W hW F) :
    pointsRelocalize B W S hW hS h G (pointsMap B W hW F k x) =
      pointsMap B S hS _ ((OverShriek.relocalizePresheafFunctor h).map k)
        (pointsRelocalize B W S hW hS h F x) := by
  induction x using Quot.ind with | _ p =>
  rfl


/-! ### Points of a representable presheaf over two bases -/

section Representable

variable (U : BigFppfOver B W hW)

/-- A field-valued point of the representable presheaf of an object `U` of the big fppf site of
`W`, read as one of the representable presheaf of `U` viewed over `S`. -/
noncomputable def FieldValuedPoint.relocalizeRep
    (p : FieldValuedPoint B W hW (yoneda.obj U)) :
    FieldValuedPoint B S hS (yoneda.obj ((Over.map h).obj U)) where
  carrier := p.carrier
  field := p.field
  contained := p.contained
  toBase := p.toBase ≫ h.hom
  value := Over.homMk p.value.left (by
    have hbase : p.value.left ≫ (U.hom ≫ h) =
        (⟨p.toBase ≫ h.hom⟩ : B.obj p.contained ⟶ B.obj hS) := by
      rw [← Category.assoc, Over.w p.value]
      rfl
    exact hbase)

/-- A field-valued point of the representable presheaf of `U` viewed over `S`, read as one of the
representable presheaf of `U` over `W`: the structure morphism to `W` is the composite of the
section with that of `U`. -/
noncomputable def FieldValuedPoint.derelocalizeRep
    (q : FieldValuedPoint B S hS (yoneda.obj ((Over.map h).obj U))) :
    FieldValuedPoint B W hW (yoneda.obj U) where
  carrier := q.carrier
  field := q.field
  contained := q.contained
  toBase := (q.value.left ≫ U.hom).hom
  value := Over.homMk q.value.left rfl

/-- Reading a point of a representable presheaf over the larger base does not move the point of
the representing scheme. -/
theorem schemePoint_relocalizeRep (p : FieldValuedPoint B W hW (yoneda.obj U)) :
    schemePoint B S hS ((Over.map h).obj U)
        (FieldValuedPoint.relocalizeRep B W S hW hS h U p) = schemePoint B W hW U p :=
  rfl

/-- Reading a point of a representable presheaf back over `W` does not move the point of the
representing scheme. -/
theorem schemePoint_derelocalizeRep
    (q : FieldValuedPoint B S hS (yoneda.obj ((Over.map h).obj U))) :
    schemePoint B W hW U (FieldValuedPoint.derelocalizeRep B W S hW hS h U q) =
      schemePoint B S hS ((Over.map h).obj U) q :=
  rfl

/-! ### The chart comparison on points -/

variable {F} (a : yoneda.obj U ⟶ F)

/-- **Reading a chart over the larger base agrees with reading its points over the larger base.**
Both sides read off the factorization through `W` that the section carries. -/
theorem class_map_relocalizeChart_relocalizeRep
    (p : FieldValuedPoint B W hW (yoneda.obj U)) :
    (FieldValuedPoint.map B S hS _ (relocalizeChart B W S hW hS h a)
        (FieldValuedPoint.relocalizeRep B W S hW hS h U p)).class B S hS _ =
      (FieldValuedPoint.relocalize B W S hW hS h F
        (FieldValuedPoint.map B W hW _ a p)).class B S hS _ := by
  set e : (Over.mk (p.value.left ≫ U.hom) : BigFppfOver B W hW) ⟶
      Over.mk (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hW) :=
    Over.homMk (𝟙 _) (by rw [Category.id_comp]; exact (Over.w p.value).symm) with hedef
  have heval : a.app (op (Over.mk (p.value.left ≫ U.hom))) (Over.homMk p.value.left rfl) =
      F.map e.op (a.app (op (Over.mk (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hW))) p.value) := by
    have hcomp : (Over.homMk p.value.left rfl :
        (Over.mk (p.value.left ≫ U.hom) : BigFppfOver B W hW) ⟶ U) = e ≫ p.value := by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, hedef]
      have hleft : p.value.left = 𝟙 _ ≫ p.value.left := (Category.id_comp _).symm
      exact hleft
    rw [hcomp]
    exact NatTrans.naturality_apply a e.op p.value
  have hgoal : (⟨(⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hW),
        a.app (op (Over.mk (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hW))) p.value⟩ :
        Σ χ : B.obj p.contained ⟶ B.obj hW, F.obj (op (Over.mk χ)))
      = ⟨p.value.left ≫ U.hom,
          a.app (op (Over.mk (p.value.left ≫ U.hom))) (Over.homMk p.value.left rfl)⟩ := by
    rw [heval]
    exact (OverShriek.sigmaMk_eq_self F _ e rfl).symm
  exact class_eq_class_of_dominates B S hS
    ⟨𝟙 _, Subtype.ext ((OverShriek.sigmaMk_eq_self F _ _ rfl).trans hgoal)⟩

/-- The converse comparison: a field-valued point of the extended chart's source read back over
`W` has the same image. -/
theorem class_relocalize_map_derelocalizeRep
    (q : FieldValuedPoint B S hS (yoneda.obj ((Over.map h).obj U))) :
    (FieldValuedPoint.relocalize B W S hW hS h F
        (FieldValuedPoint.map B W hW _ a
          (FieldValuedPoint.derelocalizeRep B W S hW hS h U q))).class B S hS _ =
      (FieldValuedPoint.map B S hS _ (relocalizeChart B W S hW hS h a) q).class B S hS _ := by
  have hw : q.value.left ≫ (U.hom ≫ h) = (⟨q.toBase⟩ : B.obj q.contained ⟶ B.obj hS) :=
    Over.w q.value
  have hw' : q.value.left.hom ≫ U.hom.hom ≫ h.hom = q.toBase := congrArg (fun k => k.hom) hw
  exact class_eq_class_of_dominates B S hS
    ⟨Over.homMk (𝟙 _) (by
        ext
        have hbase : 𝟙 _ ≫ q.toBase = (q.value.left ≫ U.hom).hom ≫ h.hom :=
          (Category.id_comp _).trans (hw'.symm.trans (Category.assoc _ _ _).symm)
        exact hbase),
      Subtype.ext (OverShriek.sigmaMk_eq_self F _ _ rfl)⟩


end Representable

/-! ### The topology on the points of a lower-shriek extension -/

/-- The comparison `AlgebraicGeometry.relocalizeBaseHom` does not move the point of the
representing scheme: it is the identity on underlying schemes. -/
theorem schemePoint_map_relocalizeBaseHom {U' : BigFppfOver B S hS} {ψ : U'.left ⟶ B.obj hW}
    (hψ : ψ ≫ h = U'.hom) (q : FieldValuedPoint B S hS (yoneda.obj U')) :
    schemePoint B S hS ((Over.map h).obj (Over.mk ψ))
        (FieldValuedPoint.map B S hS (yoneda.obj U')
          (yoneda.map (relocalizeBaseHom B W S hW hS h hψ)) q) =
      schemePoint B S hS U' q := by
  have hid : (BigFppfOver.toScheme B S hS).map (relocalizeBaseHom B W S hW hS h hψ) = 𝟙 _ := by
    have hleft : B.inclusion.map (relocalizeBaseHom B W S hW hS h hψ).left = 𝟙 _ := by
      rw [relocalizeBaseHom_left]
      exact B.inclusion.map_id _
    exact hleft
  rw [schemePoint_map_yoneda, hid]
  rfl

/-- **The topology on the points of a lower-shriek extension is the topology of the original
presheaf.** A set of points of `Λ_h F` is open for the topology detected by scheme-valued points
over `S` exactly when the corresponding set of points of `F` is open for the topology detected by
scheme-valued points over `W`: every scheme-valued point of `Λ_h F` is the extension of one of
`F`, up to an isomorphism of the site which is the identity on underlying schemes, and
corresponding scheme-valued points cut out the same subsets of the same scheme. -/
theorem isOpen_pointsRelocalize_iff
    (V : Set (points B S hS ((OverShriek.relocalizePresheafFunctor h).obj F))) :
    @IsOpen _ (pointTopology B S hS _) V ↔
      @IsOpen _ (pointTopology B W hW F) (pointsRelocalize B W S hW hS h F ⁻¹' V) := by
  rw [isOpen_pointTopology_iff, isOpen_pointTopology_iff]
  constructor
  · intro hV U a
    obtain ⟨V₀, hV₀open, hV₀⟩ := hV ((Over.map h).obj U) (relocalizeChart B W S hW hS h a)
    refine ⟨V₀, hV₀open, fun p => ?_⟩
    have hp := hV₀ (FieldValuedPoint.relocalizeRep B W S hW hS h U p)
    rw [Set.mem_preimage, pointsMap_class,
      class_map_relocalizeChart_relocalizeRep B W S hW hS h U a p] at hp
    rwa [Set.mem_preimage, Set.mem_preimage, pointsMap_class, pointsRelocalize_class,
      ← schemePoint_relocalizeRep B W S hW hS h U p]
  · intro hV U' a'
    obtain ⟨ψ, hψ, a, hae⟩ := exists_relocalizeChart B W S hW hS h U' a'
    obtain ⟨V₀, hV₀open, hV₀⟩ := hV (Over.mk ψ) a
    refine ⟨V₀, hV₀open, fun q => ?_⟩
    have hq := hV₀ (FieldValuedPoint.derelocalizeRep B W S hW hS h (Over.mk ψ)
      (FieldValuedPoint.map B S hS (yoneda.obj U')
        (yoneda.map (relocalizeBaseHom B W S hW hS h hψ)) q))
    rw [Set.mem_preimage, Set.mem_preimage, pointsMap_class, pointsRelocalize_class,
      class_relocalize_map_derelocalizeRep B W S hW hS h (Over.mk ψ) a,
      schemePoint_derelocalizeRep, schemePoint_map_relocalizeBaseHom] at hq
    rwa [Set.mem_preimage, pointsMap_class, hae, FieldValuedPoint.map_comp]

/-- **Reading points over the larger base is a closed map.** It is a bijection under which the
two topologies correspond, so it carries the complement of a closed set to an open set. -/
theorem isClosedMap_pointsRelocalize :
    @IsClosedMap _ _ (pointTopology B W hW F)
      (pointTopology B S hS ((OverShriek.relocalizePresheafFunctor h).obj F))
      (pointsRelocalize B W S hW hS h F) := by
  let _ := pointTopology B W hW F
  let _ := pointTopology B S hS ((OverShriek.relocalizePresheafFunctor h).obj F)
  intro C hC
  rw [← isOpen_compl_iff,
    ← Set.image_compl_eq (pointsRelocalize_bijective B W S hW hS h F),
    isOpen_pointsRelocalize_iff,
    Set.preimage_image_eq _ (pointsRelocalize_injective B W S hW hS h F)]
  exact hC.isOpen_compl

/-- Reading points over the larger base is continuous. -/
theorem continuous_pointsRelocalize :
    @Continuous _ _ (pointTopology B W hW F)
      (pointTopology B S hS ((OverShriek.relocalizePresheafFunctor h).obj F))
      (pointsRelocalize B W S hW hS h F) :=
  continuous_def.2 fun _ hV => (isOpen_pointsRelocalize_iff B W S hW hS h F _).1 hV

/-! ### Closedness on points and a change of base scheme -/

/-- **A morphism of presheaves on the big fppf site of `W` is closed on points as soon as its
lower-shriek extension is.** Reading points over the larger base is a homeomorphism commuting with
the two maps on points, so one is closed exactly when the other is. -/
theorem isClosedMorphism_of_relocalizeMap {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (k : X ⟶ Y)
    (hk : IsClosedMorphism B S hS ((OverShriek.relocalizePresheafFunctor h).map k)) :
    IsClosedMorphism B W hW k := by
  let _ := pointTopology B W hW X
  let _ := pointTopology B W hW Y
  let _ := pointTopology B S hS ((OverShriek.relocalizePresheafFunctor h).obj X)
  let _ := pointTopology B S hS ((OverShriek.relocalizePresheafFunctor h).obj Y)
  intro C hC
  have himg : pointsRelocalize B W S hW hS h Y '' (pointsMap B W hW X k '' C) =
      pointsMap B S hS _ ((OverShriek.relocalizePresheafFunctor h).map k) ''
        (pointsRelocalize B W S hW hS h X '' C) := by
    rw [← Set.image_comp, ← Set.image_comp]
    exact Set.image_congr' (fun x => pointsRelocalize_naturality B W S hW hS h k x)
  rw [← Set.preimage_image_eq (pointsMap B W hW X k '' C)
    (pointsRelocalize_injective B W S hW hS h Y), himg]
  exact IsClosed.preimage (continuous_pointsRelocalize B W S hW hS h Y)
    (hk _ (isClosedMap_pointsRelocalize B W S hW hS h X C hC))

end Space

end AlgebraicGeometry

end
