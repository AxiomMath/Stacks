module

public import StacksFrontier.Homology.DerivedCategory.PerfectApproximation

/-!
# A summand whose complement is built from positive shifts

Fix an abelian category `C` with a derived category, and let `R ≅ P ⊕ Q` in `D(C)` with `Q` a
finite direct sum of *positive* shifts `P⟦j⟧`, `j ≥ 1`. If the cohomology of `P` vanishes above
a degree `b`, then the cohomology of each `P⟦j⟧` vanishes in every degree `≥ b`, hence so does
that of `Q`, and the inclusion `P ⟶ R` is an isomorphism on cohomology in every degree `> b` —
"the highest degree cohomology sheaf of `R` equals that of `P`".

That sentence, and the cohomological step of the induction that follows it, are the content of
[Stacks, Tag 09IN], the remark refining [Stacks, Tag 09IM]. In the remark `R` is a perfect
object lifting `P` from a quasi-compact open `U` to the whole scheme, and the splitting
`R|_U = P ⊕ P^{⊕n_1}⟦1⟧ ⊕ ⋯ ⊕ P^{⊕n_m}⟦m⟧` is read off the construction in the proof of 09IM;
the remark then iterates the construction and takes cones to push the agreement of cohomology
sheaves below any prescribed degree. Nothing in this file is about schemes, perfectness or
support: the statements here are the degree bookkeeping, for an arbitrary abelian category.

The predicate used throughout is `DerivedCategory.ApproximatesFrom`, the library's own
"isomorphism on `H^i` for `i > m`, epimorphism for `i = m`", so that the characterization
`DerivedCategory.approximatesFrom_iff_isZero_homology_obj₃` can be used directly.

## Main results

* `DerivedCategory.isZero_homology_shift_add_iff`: `H^i(X⟦n⟧) = 0 ↔ H^{i+n}(X) = 0`, the
  arbitrary-shift form of `DerivedCategory.isZero_homology_shift_iff`.
* `DerivedCategory.isZero_homology_shift_of_one_le`: a positive shift of an object whose
  cohomology vanishes above `b` has vanishing cohomology in every degree `≥ b`.
* `DerivedCategory.isZero_homology_biprod_of_isZero`: cohomology vanishing on two objects
  vanishes on their biproduct.
* `DerivedCategory.approximatesFrom_biprod_inl_iff`: the inclusion of a summand approximates the
  biproduct from `m` exactly when the other summand has vanishing cohomology in all degrees
  `≥ m`. With the two previous results this is the second sentence of [Stacks, Tag 09IN].
* `DerivedCategory.approximatesFrom_mor₂_iff`: for a distinguished triangle, the *second*
  morphism approximates the third vertex from `m` exactly when the first vertex has vanishing
  cohomology in all degrees `> m`. This is the cohomological step of the induction in
  [Stacks, Tag 09IN]: after replacing the lift by the cone of a map out of a perfect object
  `Q'`, the cohomology of the new restriction agrees with that of `P` wherever `Q'` has none.
* `CategoryTheory.Limits.Biprod.shear_hom_comp`: the normal form of a map
  `φ : Q ⊞ Q' ⟶ P ⊞ Q` whose restriction to the first summand is the inclusion of `Q`. After the
  shear automorphism of the source it is `𝟙 Q ⊕ c` for `c : Q' ⟶ P` read off `φ`.
* `CategoryTheory.Limits.Biprod.nonempty_iso_of_distTriang_biprod_map_id` and
  `CategoryTheory.Limits.Biprod.nonempty_iso_of_distTriang_biprod_inl_comp`: the cone of
  `𝟙 Q ⊕ c`, and hence the cone of such a `φ`, is the cone of `c`, by an isomorphism that
  carries the map into the one cone to the map into the other. This is the *object* step of the
  induction in [Stacks, Tag 09IN], the one that identifies what the cone of the second
  application of [Stacks, Tag 09IM] actually is; `approximatesFrom_mor₂_iff` then turns it into
  a degree range, and the compatibility is what keeps the resulting approximating map equal to
  `biprod.inl ≫ v` instead of merely existing.

## Implementation notes

`DerivedCategory.isZero_homology_shift_iff` in
`StacksFrontier/Homology/DerivedCategory/PerfectApproximation.lean` is the case `n = 1` of
`isZero_homology_shift_add_iff`; it is left as it stands and is not restated here.

Both `approximatesFrom_biprod_inl_iff` and `approximatesFrom_mor₂_iff` are instances of
`DerivedCategory.approximatesFrom_iff_isZero_homology_obj₃`, the first at the split triangle of a
binary biproduct and the second at the rotation of the given triangle. Stating them separately is
what makes them usable without naming the triangle: a consumer of the first has a splitting and
not a triangle, and a consumer of the second has a cone and wants the map into it.

The cone identification is the octahedral axiom applied to
`biprod.map (𝟙 Q) c ≫ biprod.fst = biprod.fst`, not the direct sum of two distinguished
triangles: the cones of the two projections are a shift of the complementary summand in each
case, so the octahedron's fourth compatibility pins its middle morphism down as `c⟦1⟧` against
the split mono `P ⟶ Q ⊞ P`, and no comparison of a product triangle with a biproduct is needed.
The shear is what removes the one piece of `φ` that the hypothesis does not determine, its
`Q' ⟶ Q` component; it is an automorphism because the endomorphism it subtracts from the
identity squares to zero, so nothing about `Q` or `Q'` is used.

Both cone identifications carry the compatibility of the isomorphism with the two maps into the
cones, which is the second component of the comparison of distinguished triangles produced by
`CategoryTheory.Pretriangulated.exists_iso_of_arrow_iso`. Two points of hygiene make that
component usable. The sign by which the thrice-rotated triangle on `c` differs from the
octahedron's is absorbed on the *source* of the comparison, so that the second components are
compared without one. And the rotated triangles are restated as `Triangle.mk`s with reduced
vertices: `CategoryTheory.Pretriangulated.Triangle.rotate` is not reducible at `implicit`
transparency, so a rewrite under it silently produces a term that `rw` and `simp` then decline
to work in.

## References

* [Stacks Project, Tag 09IN](https://stacks.math.columbia.edu/tag/09IN)
* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
open CategoryTheory.Pretriangulated

namespace CategoryTheory.Limits.Biprod

/-! ### The shear automorphism, and the normal form of the map coned off in [Stacks, Tag 09IN]

The induction of [Stacks, Tag 09IN] applies the construction of [Stacks, Tag 09IM] a second
time, to the inclusion of the complement `Q` into `R|_U = P ⊕ Q`, and cones off the resulting
morphism. Over `U` that morphism is a map `φ : Q ⊕ Q' ⟶ P ⊕ Q` whose restriction to the `Q`
summand is, by the compatibility clause of 09IM, exactly the inclusion of `Q`. The two lemmas
here put such a `φ` in normal form: after an automorphism of the source — a shear, which is what
makes the unknown component `Q' ⟶ Q` disappear — it becomes `𝟙_Q ⊕ c` for the single map
`c : Q' ⟶ P` read off `φ`. So the cone of `φ` is the cone of `c`, and the cohomology of the new
lift is governed by `Q'` alone, which is what
`DerivedCategory.approximatesFrom_mor₂_iff` below then converts into a degree range.

This part is pure additive algebra: no triangulation, no abelian hypothesis. -/

section Shear

variable {D : Type*} [Category D] [Preadditive D] [HasBinaryBiproducts D]

/-- **The shear automorphism of a binary biproduct** attached to `d : Q' ⟶ Q`, acting as
`(x, y) ↦ (x - d y, y)`. It is an automorphism because the endomorphism it subtracts from the
identity squares to zero. -/
@[simps]
noncomputable def shear {Q Q' : D} (d : Q' ⟶ Q) : (Q ⊞ Q') ≅ (Q ⊞ Q') where
  hom := 𝟙 _ - biprod.snd ≫ d ≫ biprod.inl
  inv := 𝟙 _ + biprod.snd ≫ d ≫ biprod.inl
  hom_inv_id := by
    simp only [Preadditive.sub_comp, Preadditive.comp_add, Category.id_comp, Category.comp_id,
      Category.assoc, biprod.inl_snd_assoc, zero_comp, comp_zero]
    abel
  inv_hom_id := by
    simp only [Preadditive.add_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id,
      Category.assoc, biprod.inl_snd_assoc, zero_comp, comp_zero]
    abel

/-- **Normal form of a map out of `Q ⊕ Q'` that is the inclusion on `Q`.** If
`φ : Q ⊞ Q' ⟶ P ⊞ Q` restricts on the first summand to `biprod.inr`, then after the shear by its
`Q' ⟶ Q` component it is the direct sum of `𝟙 Q` with its `Q' ⟶ P` component, read into
`P ⊞ Q` through the braiding.

This is the step that makes the cone of `φ` the cone of `c`: the identity summand contributes a
zero cone, and the unknown component `Q' ⟶ Q` is sheared away rather than estimated. -/
theorem shear_hom_comp {P Q Q' : D} (φ : Q ⊞ Q' ⟶ P ⊞ Q)
    (hφ : (biprod.inl : Q ⟶ Q ⊞ Q') ≫ φ = (biprod.inr : Q ⟶ P ⊞ Q)) :
    (shear ((biprod.inr : Q' ⟶ Q ⊞ Q') ≫ φ ≫ (biprod.snd : P ⊞ Q ⟶ Q))).hom ≫ φ =
      biprod.map (𝟙 Q) ((biprod.inr : Q' ⟶ Q ⊞ Q') ≫ φ ≫ (biprod.fst : P ⊞ Q ⟶ P)) ≫
        (biprod.braiding Q P).hom := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;>
    simp [shear, Category.assoc, reassoc_of% hφ]

end Shear

/-! ### The cone of such a map is the cone of its `Q' ⟶ P` component -/

section Cone

open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasBinaryBiproducts D]

omit [IsTriangulated D] in
/-- The split triangle `B ⟶ A ⊞ B ⟶ A ⟶ B⟦1⟧` of a binary biproduct, with the projection as its
second morphism. This is `binaryBiproductTriangle` read through the braiding. -/
theorem biprod_inr_fst_distinguished (A B : D) :
    Triangle.mk (biprod.inr : B ⟶ A ⊞ B) (biprod.fst : A ⊞ B ⟶ A)
      (0 : A ⟶ B⟦(1 : ℤ)⟧) ∈ distTriang D := by
  refine isomorphic_distinguished _ (binaryBiproductTriangle_distinguished B A) _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (biprod.braiding A B) (Iso.refl _) ?_ ?_ ?_
  · apply biprod.hom_ext <;> simp [binaryBiproductTriangle]
  · apply biprod.hom_ext' <;> simp [binaryBiproductTriangle]
  · simp [binaryBiproductTriangle]

omit [Preadditive D] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] [HasBinaryBiproducts D] in
/-- An isomorphism `Z⟦n⟧ ≅ Z'⟦n⟧` compatible with the shifts of `u : X ⟶ Z` and `u' : X ⟶ Z'`
descends to an isomorphism `Z ≅ Z'` carrying `u` to `u'`, the shift being an equivalence. -/
theorem exists_iso_comp_eq_of_shiftFunctor_map {X Z Z' : D} (n : ℤ) {u : X ⟶ Z} {u' : X ⟶ Z'}
    (e : Z⟦n⟧ ≅ Z'⟦n⟧) (h : u'⟦n⟧' ≫ e.inv = u⟦n⟧') : ∃ ez : Z ≅ Z', u ≫ ez.hom = u' :=
  ⟨(shiftFunctor D n).preimageIso e, (shiftFunctor D n).map_injective (by simp [← h])⟩

/-- **The cone of `𝟙_Q ⊕ c` is the cone of `c`, compatibly with the maps into the two cones.**
For `c : Q' ⟶ P`, any cone of `biprod.map (𝟙 Q) c : Q ⊞ Q' ⟶ Q ⊞ P` is isomorphic to any cone
of `c`: the identity summand contributes nothing. The isomorphism identifies the restriction of
`v : Q ⊞ P ⟶ Z` to the second summand with the map `v' : P ⟶ Z'` of the given triangle on `c`,
so a consumer keeps hold of the map into the cone and not merely of the cone.

The proof is the octahedral axiom applied to the factorization
`biprod.map (𝟙 Q) c ≫ biprod.fst = biprod.fst`. The cones of the two projections are `P⟦1⟧` and
`Q'⟦1⟧`, so the octahedron produces a distinguished triangle
`Z ⟶ Q'⟦1⟧ ⟶ P⟦1⟧ ⟶ Z⟦1⟧` whose middle morphism its fourth compatibility pins down as `c⟦1⟧`,
the inclusion `P ⟶ Q ⊞ P` being a split mono. Comparing that triangle with the shift of the one
given for `c` identifies `Z⟦1⟧` with `Z'⟦1⟧`; the comparison is a morphism of triangles, and its
second component — carried by `CategoryTheory.Pretriangulated.exists_iso_of_arrow_iso` and kept
rather than discarded — is the stated compatibility, read back down through the shift, which is
an equivalence. -/
theorem nonempty_iso_of_distTriang_biprod_map_id {Q Q' P Z Z' : D} (c : Q' ⟶ P)
    {v : Q ⊞ P ⟶ Z} {w : Z ⟶ (Q ⊞ Q')⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (biprod.map (𝟙 Q) c) v w ∈ distTriang D)
    {v' : P ⟶ Z'} {w' : Z' ⟶ Q'⟦(1 : ℤ)⟧}
    (hT' : Triangle.mk c v' w' ∈ distTriang D) :
    ∃ e : Z ≅ Z', (biprod.inr : P ⟶ Q ⊞ P) ≫ v ≫ e.hom = v' := by
  have hcomm : biprod.map (𝟙 Q) c ≫ (biprod.fst : Q ⊞ P ⟶ Q) = (biprod.fst : Q ⊞ Q' ⟶ Q) := by
    simp
  have h₂₃ : Triangle.mk (biprod.fst : Q ⊞ P ⟶ Q) (0 : Q ⟶ P⟦(1 : ℤ)⟧)
      (-(shiftFunctor D (1 : ℤ)).map (biprod.inr : P ⟶ Q ⊞ P)) ∈ distTriang D :=
    rot_of_distTriang _ (biprod_inr_fst_distinguished Q P)
  have h₁₃ : Triangle.mk (biprod.fst : Q ⊞ Q' ⟶ Q) (0 : Q ⟶ Q'⟦(1 : ℤ)⟧)
      (-(shiftFunctor D (1 : ℤ)).map (biprod.inr : Q' ⟶ Q ⊞ Q')) ∈ distTriang D :=
    rot_of_distTriang _ (biprod_inr_fst_distinguished Q Q')
  let O := someOctahedron hcomm hT h₂₃ h₁₃
  -- the middle morphism of the octahedron triangle is `c⟦1⟧`
  have hm₃ : O.m₃ = (shiftFunctor D (1 : ℤ)).map c := by
    refine (cancel_mono ((shiftFunctor D (1 : ℤ)).map (biprod.inr : P ⟶ Q ⊞ P))).1 ?_
    have h := O.comm₄
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, neg_inj] at h
    rw [← h, ← Functor.map_comp, ← Functor.map_comp, biprod.inr_map]
  -- the octahedron triangle, rotated so that its first morphism is `c⟦1⟧`
  have hO : Triangle.mk ((shiftFunctor D (1 : ℤ)).map c)
      ((-(shiftFunctor D (1 : ℤ)).map (biprod.inr : P ⟶ Q ⊞ P)) ≫
        (shiftFunctor D (1 : ℤ)).map v)
      (-(shiftFunctor D (1 : ℤ)).map O.m₁) ∈ distTriang D := by
    have h := rot_of_distTriang _ O.mem
    rwa [hm₃] at h
  -- the triangle given for `c`, rotated three times
  have hS : Triangle.mk (-(shiftFunctor D (1 : ℤ)).map c) (-(shiftFunctor D (1 : ℤ)).map v')
      (-(shiftFunctor D (1 : ℤ)).map w') ∈ distTriang D :=
    rot_of_distTriang _ (rot_of_distTriang _ (rot_of_distTriang _ hT'))
  -- the two first morphisms differ by a sign, absorbed on the source so that the second
  -- components of the comparison are compared without one
  let eneg : (Q'⟦(1 : ℤ)⟧) ≅ (Q'⟦(1 : ℤ)⟧) :=
    { hom := -𝟙 _, inv := -𝟙 _, hom_inv_id := by simp, inv_hom_id := by simp }
  obtain ⟨e, -, he₂⟩ := exists_iso_of_arrow_iso _ _ hS hO
    (Arrow.isoMk eneg (Iso.refl _) (by
      change (-𝟙 ((shiftFunctor D (1 : ℤ)).obj Q')) ≫ (shiftFunctor D (1 : ℤ)).map c =
        (-(shiftFunctor D (1 : ℤ)).map c) ≫ 𝟙 ((shiftFunctor D (1 : ℤ)).obj P)
      simp))
  -- the second compatibility of that comparison, with the sign already cancelled
  have he₂' : e.hom.hom₂ = 𝟙 ((shiftFunctor D (1 : ℤ)).obj P) := he₂
  have hc₂ := e.hom.comm₂
  simp only [Triangle.mk_mor₂, he₂', Preadditive.neg_comp] at hc₂
  have hc₂' : (shiftFunctor D (1 : ℤ)).map v' ≫ e.hom.hom₃ =
      (shiftFunctor D (1 : ℤ)).map (biprod.inr : P ⟶ Q ⊞ P) ≫
        (shiftFunctor D (1 : ℤ)).map v :=
    neg_inj.1 (hc₂.trans (Category.id_comp _))
  obtain ⟨ez, hez⟩ := exists_iso_comp_eq_of_shiftFunctor_map (1 : ℤ)
    (Triangle.π₃.mapIso e.symm)
    (hc₂'.trans (Functor.map_comp _ _ _).symm)
  exact ⟨ez, (Category.assoc _ _ _).symm.trans hez⟩

/-- **The cone of a map out of `Q ⊕ Q'` that is the inclusion on `Q` is the cone of its
`Q' ⟶ P` component, compatibly with the maps into the two cones.** This is `shear_hom_comp` fed
into `nonempty_iso_of_distTriang_biprod_map_id`, and it is the step the induction of
[Stacks, Tag 09IN] performs: coning off the second application of [Stacks, Tag 09IM] leaves the
cone of a single map `Q' ⟶ P`, so the cohomology of the new lift is controlled by `Q'` alone.

The isomorphism carries `biprod.inl ≫ v : P ⟶ Z`, the restriction to the `P` summand of the map
into the cone of `φ`, to the map `v' : P ⟶ Z'` into the cone of the component. That is what the
remark needs: its conclusion names the map to the ambient object, not only the object. The
compatibility comes from the one proved for `nonempty_iso_of_distTriang_biprod_map_id` together
with the second component of the comparison of triangles along the shear, the braiding turning
`biprod.inl : P ⟶ P ⊞ Q` into `biprod.inr : P ⟶ Q ⊞ P`. -/
theorem nonempty_iso_of_distTriang_biprod_inl_comp {P Q Q' Z Z' : D} (φ : Q ⊞ Q' ⟶ P ⊞ Q)
    (hφ : (biprod.inl : Q ⟶ Q ⊞ Q') ≫ φ = (biprod.inr : Q ⟶ P ⊞ Q))
    {v : P ⊞ Q ⟶ Z} {w : Z ⟶ (Q ⊞ Q')⟦(1 : ℤ)⟧}
    (hT : Triangle.mk φ v w ∈ distTriang D)
    {v' : P ⟶ Z'} {w' : Z' ⟶ Q'⟦(1 : ℤ)⟧}
    (hT' : Triangle.mk ((biprod.inr : Q' ⟶ Q ⊞ Q') ≫ φ ≫ (biprod.fst : P ⊞ Q ⟶ P)) v' w'
      ∈ distTriang D) :
    ∃ e : Z ≅ Z', (biprod.inl : P ⟶ P ⊞ Q) ≫ v ≫ e.hom = v' := by
  obtain ⟨Z₀, v₀, w₀, hT₀⟩ := distinguished_cocone_triangle
    (biprod.map (𝟙 Q) ((biprod.inr : Q' ⟶ Q ⊞ Q') ≫ φ ≫ (biprod.fst : P ⊞ Q ⟶ P)))
  obtain ⟨e₀, he₀⟩ := nonempty_iso_of_distTriang_biprod_map_id _ hT₀ hT'
  have harr : (shear ((biprod.inr : Q' ⟶ Q ⊞ Q') ≫ φ ≫ (biprod.snd : P ⊞ Q ⟶ Q))).symm.hom ≫
      biprod.map (𝟙 Q) ((biprod.inr : Q' ⟶ Q ⊞ Q') ≫ φ ≫ (biprod.fst : P ⊞ Q ⟶ P)) =
      φ ≫ (biprod.braiding Q P).symm.hom := by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_comp_inv, Category.assoc,
      ← shear_hom_comp φ hφ, Iso.inv_hom_id_assoc]
  obtain ⟨e, -, he₂⟩ := exists_iso_of_arrow_iso _ _ hT hT₀ (Arrow.isoMk _ _ harr)
  have he₂' : e.hom.hom₂ = (biprod.braiding Q P).symm.hom := he₂
  have hc₂ := e.hom.comm₂
  simp only [Triangle.mk_mor₂, he₂'] at hc₂
  have hbr : (biprod.inl : P ⟶ P ⊞ Q) ≫ (biprod.braiding Q P).symm.hom =
      (biprod.inr : P ⟶ Q ⊞ P) := by
    refine biprod.hom_ext _ _ ?_ ?_ <;> simp [biprod.braiding]
  refine ⟨Triangle.π₃.mapIso e ≪≫ e₀, ?_⟩
  change _ ≫ v ≫ e.hom.hom₃ ≫ e₀.hom = _
  rwa [reassoc_of% hc₂, ← Category.assoc, hbr]

end Cone

end CategoryTheory.Limits.Biprod

namespace DerivedCategory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-! ### Cohomology of shifts -/

/-- The cohomology functors of the derived category form a shift sequence; this is the resulting
comparison `H^i(X⟦n⟧) ≅ H^j(X)` for `i + n = j`. The case `n = 1` is
`DerivedCategory.homologyShiftIso`. -/
noncomputable def homologyShiftIsoAdd (n i j : ℤ) (h : i + n = j) :
    shiftFunctor (DerivedCategory C) n ⋙ homologyFunctor C i ≅ homologyFunctor C j :=
  (homologyFunctor C 0).shiftIso n i j (by lia)

/-- `H^i(X⟦n⟧)` vanishes exactly when `H^{i+n}(X)` does. The case `n = 1` is
`DerivedCategory.isZero_homology_shift_iff`. -/
theorem isZero_homology_shift_add_iff (X : DerivedCategory C) (n i j : ℤ) (h : i + n = j) :
    IsZero ((homologyFunctor C i).obj (X⟦n⟧)) ↔ IsZero ((homologyFunctor C j).obj X) :=
  ((homologyShiftIsoAdd n i j h).app X).isZero_iff

/-- **A positive shift drops the top cohomological degree.** If the cohomology of `X` vanishes in
every degree `> b` and `n ≥ 1`, then the cohomology of `X⟦n⟧` vanishes in every degree `≥ b`.

This is why the complement in the splitting of [Stacks, Tag 09IN] contributes nothing in the top
degree: it is a sum of shifts `P⟦j⟧` with `j ≥ 1`. -/
theorem isZero_homology_shift_of_one_le (X : DerivedCategory C) (b : ℤ)
    (hX : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj X))
    (n : ℤ) (hn : 1 ≤ n) (i : ℤ) (hi : b ≤ i) :
    IsZero ((homologyFunctor C i).obj (X⟦n⟧)) :=
  (isZero_homology_shift_add_iff X n i (i + n) rfl).2 (hX (i + n) (by lia))

/-! ### Cohomology of a biproduct -/

/-- Cohomology vanishing on both summands vanishes on the biproduct: the identity of
`H^j(A ⊞ B)` is the sum of the two composites through `H^j(A)` and `H^j(B)`, and both factor
through a zero object. -/
theorem isZero_homology_biprod_of_isZero {A B : DerivedCategory C} {j : ℤ}
    (hA : IsZero ((homologyFunctor C j).obj A))
    (hB : IsZero ((homologyFunctor C j).obj B)) :
    IsZero ((homologyFunctor C j).obj (A ⊞ B)) := by
  rw [IsZero.iff_id_eq_zero, ← (homologyFunctor C j).map_id,
    show 𝟙 (A ⊞ B) = biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr by simp,
    (homologyFunctor C j).map_add, (homologyFunctor C j).map_comp,
    (homologyFunctor C j).map_comp,
    hA.eq_of_src ((homologyFunctor C j).map (biprod.inl : A ⟶ A ⊞ B)) 0,
    hB.eq_of_src ((homologyFunctor C j).map (biprod.inr : B ⟶ A ⊞ B)) 0, comp_zero, comp_zero,
    add_zero]

/-! ### Approximation by a summand, and by the map into a cone -/

/-- **The inclusion of a summand approximates the biproduct exactly as far as the other summand
allows.** `biprod.inl : P ⟶ P ⊞ Q` is an isomorphism on `H^i` for every `i > m`, and an
epimorphism on `H^m`, precisely when `Q` has vanishing cohomology in every degree `≥ m`.

This is `DerivedCategory.approximatesFrom_iff_isZero_homology_obj₃` at the split triangle
`P ⟶ P ⊞ Q ⟶ Q ⟶ P⟦1⟧` of the biproduct. -/
theorem approximatesFrom_biprod_inl_iff (P Q : DerivedCategory C) (m : ℤ) :
    ApproximatesFrom (biprod.inl : P ⟶ P ⊞ Q) m ↔
      ∀ i : ℤ, m ≤ i → IsZero ((homologyFunctor C i).obj Q) :=
  approximatesFrom_iff_isZero_homology_obj₃ (binaryBiproductTriangle P Q)
    (binaryBiproductTriangle_distinguished P Q) m

/-- **The first sentence of [Stacks, Tag 09IN], as a statement about the splitting.** If the
cohomology of `P` vanishes in every degree `> b` and that of `Q` in every degree `≥ b`, then
`biprod.inl : P ⟶ P ⊞ Q` is an isomorphism on cohomology in every degree `> b`: the highest
degree cohomology of `P ⊞ Q` is that of `P`.

The hypothesis on `Q` is what `DerivedCategory.isZero_homology_shift_of_one_le` and
`DerivedCategory.isZero_homology_biprod_of_isZero` supply when `Q` is a finite direct sum of
shifts `P⟦j⟧` with `j ≥ 1`, which is the shape the proof of [Stacks, Tag 09IM] produces. -/
theorem isIso_homology_biprod_inl_of_isZero_homology_ge (P Q : DerivedCategory C) (b : ℤ)
    (hQ : ∀ i : ℤ, b ≤ i → IsZero ((homologyFunctor C i).obj Q))
    (i : ℤ) (hi : b < i) :
    IsIso ((homologyFunctor C i).map (biprod.inl : P ⟶ P ⊞ Q)) :=
  ((approximatesFrom_biprod_inl_iff P Q b).2 hQ).1 i hi

/-- **The map into a cone approximates it exactly as far as the source allows.** For a
distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧`, the second morphism `Y ⟶ Z` is an isomorphism on
`H^i` for every `i > m` and an epimorphism on `H^m` precisely when `X` has vanishing cohomology
in every degree `> m`.

This is the cohomological step of the induction in [Stacks, Tag 09IN]: the remark replaces the
lift by the cone of a morphism out of a complex `X` whose cohomology sits in low degrees, and the
cohomology of the cone then agrees with that of `Y` wherever `X` has none. It is
`DerivedCategory.approximatesFrom_iff_isZero_homology_obj₃` at the rotation of the triangle,
whose third vertex is `X⟦1⟧`. -/
theorem approximatesFrom_mor₂_iff (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (m : ℤ) :
    ApproximatesFrom T.mor₂ m ↔
      ∀ i : ℤ, m < i → IsZero ((homologyFunctor C i).obj T.obj₁) :=
  (approximatesFrom_iff_isZero_homology_obj₃ T.rotate (rot_of_distTriang T hT) m).trans
    ⟨fun h i _ => (isZero_homology_shift_add_iff T.obj₁ 1 (i - 1) i (by lia)).1
        (h (i - 1) (by lia)),
      fun h i _ => (isZero_homology_shift_add_iff T.obj₁ 1 i (i + 1) rfl).2 (h (i + 1) (by lia))⟩

end DerivedCategory

end
